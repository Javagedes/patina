//! [`Signature`] implementation.
//!
//! Signing and verification are configured here. Certificate and signed data inspection delegate to the X.509,
//! PKCS#7, and Authenticode helpers.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use alloc::{boxed::Box, string::String, vec::Vec};
use core::cmp::Ordering;

use patina::standard::efi;

use super::{OneCrypto, ec::EcKey, rsa::RsaKey};
use crate::{
    error::{CryptoError, Result},
    service::{
        hash::{Hash, HashAlgorithm},
        signature::{
            Pkcs7CertificateLists, Pkcs7Signers, Signature, SignatureAlgorithm, Signer, SigningKey, TrustAnchorCache,
            VerifiedSignature, Verifier, X509DateTime, X509Validity,
        },
    },
};

/// The configured signing algorithm and key.
enum SignerState {
    RsaPkcs1v15 { key: RsaKey, digest: HashAlgorithm },
    RsaPss { key: RsaKey, digest: HashAlgorithm, salt_size: u16 },
    Ecdsa { key: EcKey, digest: HashAlgorithm },
    Pkcs7 { private_key: Vec<u8>, password: Option<String>, certificate: Vec<u8>, other_certificates: Vec<Vec<u8>> },
}

/// A [`Signer`] backed by the OneCrypto protocol.
struct OneCryptoSigner {
    crypto: OneCrypto,
    state: SignerState,
}

impl Signer for OneCryptoSigner {
    fn sign(&self, data: &[u8]) -> Result<Vec<u8>> {
        match &self.state {
            SignerState::RsaPkcs1v15 { key, digest } => key.pkcs1_sign(&self.crypto.hash_all(*digest, data)?),
            SignerState::RsaPss { key, digest, salt_size } => key.pss_sign(data, *digest, *salt_size),
            SignerState::Ecdsa { key, digest } => key.dsa_sign(*digest, &self.crypto.hash_all(*digest, data)?),
            SignerState::Pkcs7 { private_key, password, certificate, other_certificates } => {
                let other_certificates = other_certificates.iter().map(Vec::as_slice).collect::<Vec<_>>();
                self.crypto.pkcs7_sign(private_key, password.as_deref(), data, certificate, &other_certificates)
            }
        }
    }
}

/// The configured verification algorithm and key or trust anchor.
enum VerifierState {
    RsaPkcs1v15 { key: RsaKey, digest: HashAlgorithm },
    RsaPss { key: RsaKey, digest: HashAlgorithm, salt_size: u16 },
    Ecdsa { key: EcKey, digest: HashAlgorithm },
    Pkcs7(Vec<u8>),
    Cms(Vec<u8>),
    Authenticode(Vec<u8>),
}

/// A [`Verifier`] backed by the OneCrypto protocol.
struct OneCryptoVerifier {
    crypto: OneCrypto,
    state: VerifierState,
}

impl Verifier for OneCryptoVerifier {
    fn verify(&self, data: &[u8], signature: &[u8]) -> Result<VerifiedSignature> {
        let signer_chain = match &self.state {
            VerifierState::RsaPkcs1v15 { key, digest } => {
                key.pkcs1_verify(&self.crypto.hash_all(*digest, data)?, signature).map(|_| Vec::new())?
            }
            VerifierState::RsaPss { key, digest, salt_size } => {
                key.pss_verify(data, signature, *digest, *salt_size).map(|_| Vec::new())?
            }
            VerifierState::Ecdsa { key, digest } => {
                key.dsa_verify(*digest, &self.crypto.hash_all(*digest, data)?, signature).map(|_| Vec::new())?
            }
            VerifierState::Pkcs7(root) => self.crypto.pkcs7_verify(signature, root, data).map(|_| Vec::new())?,
            VerifierState::Cms(root) => self.crypto.cms_verify(signature, root, data)?,
            VerifierState::Authenticode(root) => self.crypto.authenticode_verify(signature, root, data)?,
        };
        Ok(VerifiedSignature::new(signer_chain))
    }
}

impl Signature for OneCrypto {
    fn new_signer(&self, algorithm: SignatureAlgorithm, key: SigningKey<'_>) -> Result<Box<dyn Signer>> {
        let raw_key = !key.certificate.is_empty() || !key.other_certificates.is_empty();
        let state = match algorithm {
            SignatureAlgorithm::RsaPkcs1v15 { .. }
            | SignatureAlgorithm::RsaPss { .. }
            | SignatureAlgorithm::Ecdsa { .. }
                if raw_key =>
            {
                return Err(CryptoError::InvalidParameter);
            }
            SignatureAlgorithm::RsaPkcs1v15 { digest } => {
                SignerState::RsaPkcs1v15 { key: self.rsa_private_key_from_pem(key.private_key, key.password)?, digest }
            }
            SignatureAlgorithm::RsaPss { digest, salt_size } => SignerState::RsaPss {
                key: self.rsa_private_key_from_pem(key.private_key, key.password)?,
                digest,
                salt_size,
            },
            SignatureAlgorithm::Ecdsa { digest } => {
                SignerState::Ecdsa { key: self.ec_private_key_from_pem(key.private_key, key.password)?, digest }
            }
            SignatureAlgorithm::Pkcs7 if key.certificate.is_empty() => return Err(CryptoError::InvalidParameter),
            SignatureAlgorithm::Pkcs7 => SignerState::Pkcs7 {
                private_key: key.private_key.to_vec(),
                password: key.password.map(String::from),
                certificate: key.certificate.to_vec(),
                other_certificates: key.other_certificates.iter().map(|c| c.to_vec()).collect(),
            },
            _ => return Err(CryptoError::Unsupported),
        };
        Ok(Box::new(OneCryptoSigner { crypto: *self, state }))
    }

    fn new_verifier(&self, algorithm: SignatureAlgorithm, certificate: &[u8]) -> Result<Box<dyn Verifier>> {
        let state = match algorithm {
            SignatureAlgorithm::RsaPkcs1v15 { digest } => {
                VerifierState::RsaPkcs1v15 { key: self.rsa_public_key_from_x509(certificate)?, digest }
            }
            SignatureAlgorithm::RsaPss { digest, salt_size } => {
                VerifierState::RsaPss { key: self.rsa_public_key_from_x509(certificate)?, digest, salt_size }
            }
            SignatureAlgorithm::Ecdsa { digest } => {
                VerifierState::Ecdsa { key: self.ec_public_key_from_x509(certificate)?, digest }
            }
            SignatureAlgorithm::Pkcs7 => VerifierState::Pkcs7(certificate.to_vec()),
            SignatureAlgorithm::Cms => VerifierState::Cms(certificate.to_vec()),
            SignatureAlgorithm::Authenticode => VerifierState::Authenticode(certificate.to_vec()),
            _ => return Err(CryptoError::Unsupported),
        };
        Ok(Box::new(OneCryptoVerifier { crypto: *self, state }))
    }

    fn verify_certificate(&self, certificate: &[u8], ca_certificate: &[u8]) -> Result<()> {
        OneCrypto::verify_certificate(self, certificate, ca_certificate)
    }

    fn verify_certificate_chain(&self, root_certificate: &[u8], chain: &[u8]) -> Result<()> {
        OneCrypto::verify_certificate_chain(self, root_certificate, chain)
    }

    fn verify_timestamp(&self, signature: &[u8], tsa_certificate: &[u8]) -> Result<efi::Time> {
        OneCrypto::verify_timestamp(self, signature, tsa_certificate)
    }

    fn verify_ekus(&self, signed_data: &[u8], required_ekus: &[&str], require_all: bool) -> Result<()> {
        OneCrypto::verify_ekus(self, signed_data, required_ekus, require_all)
    }

    fn signer_info_count(&self, signed_data: &[u8]) -> usize {
        OneCrypto::signer_info_count(self, signed_data)
    }

    fn signers(&self, signed_data: &[u8]) -> Result<Pkcs7Signers> {
        OneCrypto::signers(self, signed_data)
    }

    fn embedded_certificates(&self, signed_data: &[u8]) -> Result<Pkcs7CertificateLists> {
        OneCrypto::embedded_certificates(self, signed_data)
    }

    fn attached_content(&self, signed_data: &[u8]) -> Result<Vec<u8>> {
        OneCrypto::attached_content(self, signed_data)
    }

    fn authenticode_hash_algorithm(&self, signature: &[u8]) -> Result<HashAlgorithm> {
        OneCrypto::authenticode_hash_algorithm(self, signature)
    }

    fn trust_anchor(&self, tbs_certificate_hash: &[u8], signature: &[u8]) -> Result<Vec<u8>> {
        OneCrypto::trust_anchor(self, tbs_certificate_hash, signature)
    }

    fn new_trust_anchor_cache(&self) -> Result<Box<dyn TrustAnchorCache>> {
        OneCrypto::new_trust_anchor_cache(self)
    }

    fn subject_name(&self, certificate: &[u8]) -> Result<Vec<u8>> {
        OneCrypto::subject_name(self, certificate)
    }

    fn issuer_name(&self, certificate: &[u8]) -> Result<Vec<u8>> {
        OneCrypto::issuer_name(self, certificate)
    }

    fn common_name(&self, certificate: &[u8]) -> Result<String> {
        OneCrypto::common_name(self, certificate)
    }

    fn organization_name(&self, certificate: &[u8]) -> Result<String> {
        OneCrypto::organization_name(self, certificate)
    }

    fn certificate_version(&self, certificate: &[u8]) -> Result<usize> {
        OneCrypto::certificate_version(self, certificate)
    }

    fn serial_number(&self, certificate: &[u8]) -> Result<Vec<u8>> {
        OneCrypto::serial_number(self, certificate)
    }

    fn certificate_signature_algorithm(&self, certificate: &[u8]) -> Result<Vec<u8>> {
        OneCrypto::certificate_signature_algorithm(self, certificate)
    }

    fn tbs_certificate(&self, certificate: &[u8]) -> Result<Vec<u8>> {
        OneCrypto::tbs_certificate(self, certificate)
    }

    fn certificate_validity(&self, certificate: &[u8]) -> Result<X509Validity> {
        OneCrypto::certificate_validity(self, certificate)
    }

    fn key_usage(&self, certificate: &[u8]) -> Result<usize> {
        OneCrypto::key_usage(self, certificate)
    }

    fn extended_key_usage(&self, certificate: &[u8]) -> Result<Vec<u8>> {
        OneCrypto::extended_key_usage(self, certificate)
    }

    fn basic_constraints(&self, certificate: &[u8]) -> Result<Vec<u8>> {
        OneCrypto::basic_constraints(self, certificate)
    }

    fn certificate_extension(&self, certificate: &[u8], oid: &[u8]) -> Result<Vec<u8>> {
        OneCrypto::certificate_extension(self, certificate, oid)
    }

    fn is_public_key_supported(&self, certificate: &[u8]) -> bool {
        OneCrypto::is_public_key_supported(self, certificate)
    }

    fn certificate_from_chain(&self, chain: &[u8], index: usize) -> Result<Vec<u8>> {
        OneCrypto::certificate_from_chain(self, chain, index)
    }

    fn parse_date_time(&self, date_time: &str) -> Result<X509DateTime> {
        OneCrypto::parse_date_time(self, date_time)
    }

    fn compare_date_time(&self, first: &X509DateTime, second: &X509DateTime) -> Result<Ordering> {
        OneCrypto::compare_date_time(self, first, second)
    }

    fn asn1_get_tag(&self, data: &[u8], tag: u32) -> Result<(usize, usize)> {
        OneCrypto::asn1_get_tag(self, data, tag)
    }
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
mod tests {
    use alloc::vec;

    use super::{
        super::{
            authenticode::tests::authenticode, ec::tests::ec_protocol, hash::tests::with_sha256, pkcs7::tests::pkcs7,
            protocol::CRYPTO_NID_SHA256, rsa::tests::rsa_protocol, test_support::*,
        },
        *,
    };
    use crate::service::signature::SignatureExt;

    const PKCS1: SignatureAlgorithm = SignatureAlgorithm::RsaPkcs1v15 { digest: HashAlgorithm::Sha256 };
    const PSS: SignatureAlgorithm = SignatureAlgorithm::RsaPss { digest: HashAlgorithm::Sha256, salt_size: 32 };
    const ECDSA: SignatureAlgorithm = SignatureAlgorithm::Ecdsa { digest: HashAlgorithm::Sha256 };

    #[test]
    fn test_one_crypto_signature_rsa_hashes_pkcs1_messages() {
        let crypto = crypto(with_sha256(rsa_protocol()));
        let signature = crypto.sign(PKCS1, SigningKey::new(&[0]), &[1, 2]).expect("sign");
        // The fake signature is the fake SHA-256 digest followed by 600 filler bytes.
        assert_eq!(signature[..32], [3; 32]);
        assert_eq!(signature.len(), 632);
        assert_eq!(crypto.verify(PKCS1, &[0], &[1, 2], &signature), Ok(VerifiedSignature::default()));
        assert_eq!(crypto.verify(PKCS1, &[0], &[1, 2], &[]), Err(CryptoError::VerificationFailed));
    }

    #[test]
    fn test_one_crypto_signature_rsa_pss_signs_messages() {
        let crypto = crypto(rsa_protocol());
        let signature = crypto.sign(PSS, SigningKey::new(&[0]).with_password("pw"), &[1; 4]).expect("sign");
        assert_eq!(signature.len(), 604);
        assert_eq!(crypto.verify(PSS, &[0], &[1; 4], &[0; 32]), Ok(VerifiedSignature::default()));
        assert_eq!(crypto.verify(PSS, &[0], &[1; 4], &[]), Err(CryptoError::VerificationFailed));
        assert_eq!(crypto.new_verifier(PSS, &[]).err(), Some(CryptoError::Failed));
    }

    #[test]
    fn test_one_crypto_signature_ecdsa_hashes_messages() {
        let crypto = crypto(with_sha256(ec_protocol()));
        let signature = crypto.sign(ECDSA, SigningKey::new(&[0]), &[1]).expect("sign");
        assert_eq!(signature, vec![CRYPTO_NID_SHA256 as u8]);
        assert_eq!(crypto.verify(ECDSA, &[0; 3], &[1], &signature), Ok(VerifiedSignature::default()));
        assert_eq!(crypto.verify(ECDSA, &[0; 3], &[1], &[0]), Err(CryptoError::VerificationFailed));
        let sha1 = SignatureAlgorithm::Ecdsa { digest: HashAlgorithm::Sha1 };
        assert_eq!(crypto.sign(sha1, SigningKey::new(&[0]), &[1]), Err(CryptoError::Unsupported));
    }

    #[test]
    fn test_one_crypto_signature_pkcs7_and_cms() {
        let crypto = crypto_with_frees(pkcs7(), 2);
        let key = SigningKey::new(&[0]).with_password("pw").with_certificates(&[1], &[]);
        assert_eq!(crypto.sign(SignatureAlgorithm::Pkcs7, key, &[5]), Ok(vec![5, 1, 1]));
        let pkcs7 = SignatureAlgorithm::Pkcs7;
        assert_eq!(crypto.verify(pkcs7, &[], &[5], &[5]), Ok(VerifiedSignature::default()));
        assert_eq!(crypto.verify(pkcs7, &[], &[5], &[6]), Err(CryptoError::VerificationFailed));
        let cms = SignatureAlgorithm::Cms;
        assert_eq!(crypto.verify(cms, &[], &[5], &[5]), Ok(VerifiedSignature::new(vec![vec![9]])));
        assert_eq!(crypto.verify(cms, &[], &[5], &[6]), Err(CryptoError::VerificationFailed));
    }

    #[test]
    fn test_one_crypto_signature_authenticode() {
        let crypto = crypto_with_frees(authenticode(), 1);
        let algorithm = SignatureAlgorithm::Authenticode;
        assert_eq!(crypto.verify(algorithm, &[], &[1], &[1]), Ok(VerifiedSignature::new(vec![vec![5], vec![6]])));
        assert_eq!(crypto.verify(algorithm, &[], &[2], &[1]), Err(CryptoError::VerificationFailed));
    }

    #[test]
    fn test_one_crypto_signature_rejects_invalid_signers() {
        let crypto = crypto(pkcs7());
        let others: &[&[u8]] = &[&[2]];
        let with_certificates = SigningKey::new(&[0]).with_certificates(&[1], &[]);
        for algorithm in [PKCS1, PSS, ECDSA] {
            assert_eq!(crypto.new_signer(algorithm, with_certificates).err(), Some(CryptoError::InvalidParameter));
        }
        let pkcs7 = SignatureAlgorithm::Pkcs7;
        assert_eq!(crypto.new_signer(pkcs7, SigningKey::new(&[0])).err(), Some(CryptoError::InvalidParameter));
        let with_others = SigningKey::new(&[0]).with_certificates(&[1], others);
        assert_eq!(crypto.sign(pkcs7, with_others, &[5]), Err(CryptoError::Unsupported));
        for algorithm in [SignatureAlgorithm::Cms, SignatureAlgorithm::Authenticode] {
            assert_eq!(crypto.new_signer(algorithm, SigningKey::new(&[0])).err(), Some(CryptoError::Unsupported));
        }
    }
}
