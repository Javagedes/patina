//! Signature service: signing, verification, and the certificate and signed data inspection that supports it.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use alloc::{boxed::Box, string::String, vec::Vec};
use core::cmp::Ordering;

use crate::standard::efi;

use crate::crypto::{error::Result, hash::HashAlgorithm};

#[cfg(any(test, feature = "mockall"))]
use mockall::automock;

/// Signature algorithms.
///
/// Every algorithm uses the same [`Signer::sign`] and [`Verifier::verify`] calls on `data`:
///
/// | Algorithm | `data` | `signature` | Verifier certificate |
/// | --- | --- | --- | --- |
/// | [`RsaPkcs1v15`](Self::RsaPkcs1v15) | Message | Raw signature | Signer certificate |
/// | [`RsaPss`](Self::RsaPss) | Message | Raw signature | Signer certificate |
/// | [`Ecdsa`](Self::Ecdsa) | Message | Raw `r \|\| s` signature | Signer certificate |
/// | [`Pkcs7`](Self::Pkcs7) | Content | DER PKCS#7 signed data | Trusted root |
/// | [`Cms`](Self::Cms) | Content | DER CMS signed data | Trusted root |
/// | [`Authenticode`](Self::Authenticode) | Authenticode image hash | DER PKCS#7 signed data | Trusted root |
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SignatureAlgorithm {
    /// RSASSA-PKCS1-v1_5. The message is hashed with `digest`.
    RsaPkcs1v15 {
        /// The message hash algorithm.
        digest: HashAlgorithm,
    },
    /// RSASSA-PSS. The message is hashed with `digest`, which is also used for MGF1.
    RsaPss {
        /// The message hash algorithm.
        digest: HashAlgorithm,
        /// The salt size in bytes.
        salt_size: u16,
    },
    /// ECDSA. The message is hashed with `digest`; the curve comes from the key. SHA-1 is not supported.
    Ecdsa {
        /// The message hash algorithm.
        digest: HashAlgorithm,
    },
    /// PKCS#7 signed data. Signed data may be wrapped in a `ContentInfo` structure.
    Pkcs7,
    /// CMS signed data. Verification returns the signer certificate chain. Signing is not supported.
    Cms,
    /// Authenticode signatures from PE/COFF images. Verification returns the signer certificate chain. Signing is not
    /// supported.
    Authenticode,
}

/// Private key and certificates for [`Signature::new_signer`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct SigningKey<'a> {
    /// The PEM-encoded private key.
    pub private_key: &'a [u8],
    /// The private key password.
    pub password: Option<&'a str>,
    /// The DER-encoded signing certificate. Required for [`SignatureAlgorithm::Pkcs7`].
    pub certificate: &'a [u8],
    /// Additional DER-encoded certificates, such as intermediate CAs, to embed in PKCS#7 signed data.
    pub other_certificates: &'a [&'a [u8]],
}

impl<'a> SigningKey<'a> {
    /// Creates a signing key from a PEM-encoded private key.
    pub const fn new(private_key: &'a [u8]) -> Self {
        Self { private_key, password: None, certificate: &[], other_certificates: &[] }
    }

    /// Decrypts the private key with `password`.
    #[must_use]
    pub const fn with_password(mut self, password: &'a str) -> Self {
        self.password = Some(password);
        self
    }

    /// Sets the signing certificate and additional certificates for PKCS#7 signed data.
    #[must_use]
    pub const fn with_certificates(mut self, certificate: &'a [u8], other_certificates: &'a [&'a [u8]]) -> Self {
        self.certificate = certificate;
        self.other_certificates = other_certificates;
        self
    }
}

/// The result of a successful signature verification.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct VerifiedSignature {
    /// The verified DER-encoded certificate chain, ordered from signer to trust anchor.
    ///
    /// Only [`SignatureAlgorithm::Cms`] and [`SignatureAlgorithm::Authenticode`] report a chain; it is empty for other
    /// algorithms.
    pub signer_chain: Vec<Vec<u8>>,
}

impl VerifiedSignature {
    /// Creates a verification result with `signer_chain`.
    pub const fn new(signer_chain: Vec<Vec<u8>>) -> Self {
        Self { signer_chain }
    }
}

/// A provider-specific date and time.
///
/// Consumers obtain values from [`Signature::certificate_validity`] or [`Signature::parse_date_time`], and can only
/// compare them with [`Signature::compare_date_time`] on the same provider. Providers construct values with
/// [`Self::from_provider`]; their encoding is opaque to consumers.
#[derive(Debug, PartialEq, Eq)]
pub struct X509DateTime {
    bytes: Vec<u8>,
}

impl X509DateTime {
    /// Wraps provider-encoded date and time bytes.
    ///
    /// # Safety
    ///
    /// The bytes must contain a complete, valid date/time encoding for the provider used
    /// to compare this value. Any embedded references must remain valid for this value's lifetime.
    pub unsafe fn from_provider(bytes: Vec<u8>) -> Self {
        Self { bytes }
    }

    /// Returns the provider-encoded date and time bytes.
    ///
    /// Intended for provider implementations; consumers must not interpret the encoding.
    pub fn as_provider_bytes(&self) -> &[u8] {
        &self.bytes
    }
}

/// The validity period of a certificate.
#[derive(Debug, PartialEq, Eq)]
pub struct X509Validity {
    /// Start of the validity period (notBefore).
    pub not_before: X509DateTime,
    /// End of the validity period (notAfter).
    pub not_after: X509DateTime,
}

/// Signer certificates embedded in PKCS#7 signed data.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pkcs7Signers {
    /// All DER-encoded signer certificates.
    pub certificates: Vec<Vec<u8>>,
    /// The DER-encoded trusted certificate from the signer certificates.
    pub trusted_certificate: Vec<u8>,
}

/// Certificates embedded in PKCS#7 signed data, grouped by their relationship to the signer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pkcs7CertificateLists {
    /// DER-encoded certificates chained to the signer certificate.
    pub signer_chain: Vec<Vec<u8>>,
    /// DER-encoded certificates not chained to the signer certificate.
    pub unchained: Vec<Vec<u8>>,
}

/// A cache of certificates parsed from Authenticode signatures.
///
/// The cache can be reused across signatures. Dropping it releases its provider resources.
#[cfg_attr(any(test, feature = "mockall"), automock)]
pub trait TrustAnchorCache {
    /// Behaves like [`Signature::trust_anchor`] and caches the certificates parsed from `signature`.
    fn trust_anchor(&mut self, tbs_certificate_hash: &[u8], signature: &[u8]) -> Result<Vec<u8>>;
}

/// A configured signer. Dropping it releases its provider resources.
#[cfg_attr(any(test, feature = "mockall"), automock)]
pub trait Signer {
    /// Signs `data` and returns the signature.
    fn sign(&self, data: &[u8]) -> Result<Vec<u8>>;
}

/// A configured verifier. Dropping it releases its provider resources.
#[cfg_attr(any(test, feature = "mockall"), automock)]
pub trait Verifier {
    /// Verifies `signature` over `data`.
    ///
    /// # Errors
    ///
    /// Returns [`CryptoError::VerificationFailed`](crate::crypto::error::CryptoError::VerificationFailed) if verification
    /// fails.
    fn verify(&self, data: &[u8], signature: &[u8]) -> Result<VerifiedSignature>;
}

/// Signature operations.
///
/// Equivalent to the `RsaPkcs1*`, `RsaPss*`, `EcDsa*`, `Pkcs7*`, `CmsVerify`, `Authenticode*`, `ImageTimestampVerify`,
/// `X509*`, and `Asn1GetTag` functions in `BaseCryptLib`.
///
/// Signing and verification are algorithm agile: the algorithm and key are selected once, and the returned
/// [`Signer`] or [`Verifier`] works the same way for every algorithm. Use [`SignatureExt`] for one-shot operations.
///
/// The remaining methods inspect the certificates and signed data that verification consumes. Certificates are
/// DER-encoded, and PKCS#7 signed data may be wrapped in a `ContentInfo` structure.
#[cfg_attr(any(test, feature = "mockall"), automock)]
pub trait Signature {
    /// Creates a signer for `algorithm` with `key`.
    ///
    /// # Errors
    ///
    /// - [`CryptoError::Unsupported`](crate::crypto::error::CryptoError::Unsupported) if `algorithm` does not support
    ///   signing.
    /// - [`CryptoError::InvalidParameter`](crate::crypto::error::CryptoError::InvalidParameter) if `key` is missing data the
    ///   algorithm requires.
    #[allow(clippy::needless_lifetimes, reason = "mockall requires explicit lifetimes for nested references")]
    fn new_signer<'a>(&self, algorithm: SignatureAlgorithm, key: SigningKey<'a>) -> Result<Box<dyn Signer>>;

    /// Creates a verifier for `algorithm` with the DER-encoded `certificate`.
    ///
    /// The certificate holds the signer's public key for raw signatures, or is the trusted root for signed data.
    fn new_verifier(&self, algorithm: SignatureAlgorithm, certificate: &[u8]) -> Result<Box<dyn Verifier>>;

    /// Verifies that `certificate` was issued by `ca_certificate`.
    ///
    /// # Errors
    ///
    /// Returns [`CryptoError::VerificationFailed`](crate::crypto::error::CryptoError::VerificationFailed) if verification
    /// fails.
    fn verify_certificate(&self, certificate: &[u8], ca_certificate: &[u8]) -> Result<()>;

    /// Verifies a chain of concatenated DER certificates against `root_certificate`.
    ///
    /// The first certificate in `chain` is signed by the root, and each following certificate is signed by the one
    /// before it.
    ///
    /// # Errors
    ///
    /// Returns [`CryptoError::VerificationFailed`](crate::crypto::error::CryptoError::VerificationFailed) if verification
    /// fails.
    fn verify_certificate_chain(&self, root_certificate: &[u8], chain: &[u8]) -> Result<()>;

    /// Verifies the RFC 3161 timestamp countersignature in the Authenticode `signature` against the DER-encoded
    /// `tsa_certificate`.
    ///
    /// Returns the signing time.
    ///
    /// # Errors
    ///
    /// Returns [`CryptoError::VerificationFailed`](crate::crypto::error::CryptoError::VerificationFailed) if verification
    /// fails.
    fn verify_timestamp(&self, signature: &[u8], tsa_certificate: &[u8]) -> Result<efi::Time>;

    /// Verifies that the leaf signer certificate in PKCS#7 `signed_data` has the extended key usages in
    /// `required_ekus`.
    ///
    /// Each EKU is a dotted OID string. When `require_all` is `false`, one match is sufficient. The certificate
    /// chain is not verified.
    ///
    /// # Errors
    ///
    /// Returns [`CryptoError::NotFound`](crate::crypto::error::CryptoError::NotFound) if the required EKUs are not present.
    #[allow(clippy::needless_lifetimes, reason = "mockall requires explicit lifetimes for nested references")]
    fn verify_ekus<'a>(&self, signed_data: &[u8], required_ekus: &[&'a str], require_all: bool) -> Result<()>;

    /// Returns the number of `SignerInfo` structures in PKCS#7 `signed_data`, or zero if it is invalid.
    fn signer_info_count(&self, signed_data: &[u8]) -> usize;

    /// Returns the signer certificates from PKCS#7 `signed_data`.
    fn signers(&self, signed_data: &[u8]) -> Result<Pkcs7Signers>;

    /// Returns all certificates embedded in PKCS#7 `signed_data`, grouped by whether they chain to the signer.
    fn embedded_certificates(&self, signed_data: &[u8]) -> Result<Pkcs7CertificateLists>;

    /// Returns the content attached to PKCS#7 `signed_data`.
    ///
    /// # Errors
    ///
    /// Returns [`CryptoError::NotFound`](crate::crypto::error::CryptoError::NotFound) if the signed data is detached.
    fn attached_content(&self, signed_data: &[u8]) -> Result<Vec<u8>>;

    /// Returns the algorithm used for the image hash in the Authenticode `signature`.
    ///
    /// # Errors
    ///
    /// Returns [`CryptoError::Unsupported`](crate::crypto::error::CryptoError::Unsupported) if the algorithm is not
    /// recognized.
    fn authenticode_hash_algorithm(&self, signature: &[u8]) -> Result<HashAlgorithm>;

    /// Returns the DER-encoded certificate in the Authenticode `signature` whose `TBSCertificate` digest is
    /// `tbs_certificate_hash`.
    ///
    /// The hash algorithm is selected by the length of `tbs_certificate_hash`.
    ///
    /// # Errors
    ///
    /// Returns [`CryptoError::NotFound`](crate::crypto::error::CryptoError::NotFound) if no certificate matches.
    fn trust_anchor(&self, tbs_certificate_hash: &[u8], signature: &[u8]) -> Result<Vec<u8>>;

    /// Creates a cache for repeated [`trust_anchor`](Self::trust_anchor) lookups.
    fn new_trust_anchor_cache(&self) -> Result<Box<dyn TrustAnchorCache>>;

    /// Returns the DER-encoded subject name of `certificate`.
    fn subject_name(&self, certificate: &[u8]) -> Result<Vec<u8>>;

    /// Returns the DER-encoded issuer name of `certificate`.
    fn issuer_name(&self, certificate: &[u8]) -> Result<Vec<u8>>;

    /// Returns the subject common name (CN) of `certificate`.
    ///
    /// # Errors
    ///
    /// Returns [`CryptoError::NotFound`](crate::crypto::error::CryptoError::NotFound) if the subject has no common name.
    fn common_name(&self, certificate: &[u8]) -> Result<String>;

    /// Returns the subject organization name (O) of `certificate`.
    ///
    /// # Errors
    ///
    /// Returns [`CryptoError::NotFound`](crate::crypto::error::CryptoError::NotFound) if the subject has no organization
    /// name.
    fn organization_name(&self, certificate: &[u8]) -> Result<String>;

    /// Returns the version of `certificate` as encoded in the certificate (0 for v1, 2 for v3).
    fn certificate_version(&self, certificate: &[u8]) -> Result<usize>;

    /// Returns the serial number of `certificate`.
    fn serial_number(&self, certificate: &[u8]) -> Result<Vec<u8>>;

    /// Returns the DER-encoded signature algorithm OID of `certificate`.
    fn certificate_signature_algorithm(&self, certificate: &[u8]) -> Result<Vec<u8>>;

    /// Returns the DER-encoded `TBSCertificate` of `certificate`.
    fn tbs_certificate(&self, certificate: &[u8]) -> Result<Vec<u8>>;

    /// Returns the validity period of `certificate`.
    fn certificate_validity(&self, certificate: &[u8]) -> Result<X509Validity>;

    /// Returns the key usage bit mask of `certificate`.
    fn key_usage(&self, certificate: &[u8]) -> Result<usize>;

    /// Returns the DER-encoded extended key usage extension of `certificate`.
    fn extended_key_usage(&self, certificate: &[u8]) -> Result<Vec<u8>>;

    /// Returns the DER-encoded basic constraints extension of `certificate`.
    fn basic_constraints(&self, certificate: &[u8]) -> Result<Vec<u8>>;

    /// Returns the data of the `certificate` extension identified by the DER-encoded `oid`.
    ///
    /// # Errors
    ///
    /// Returns [`CryptoError::NotFound`](crate::crypto::error::CryptoError::NotFound) if the extension is not present.
    fn certificate_extension(&self, certificate: &[u8], oid: &[u8]) -> Result<Vec<u8>>;

    /// Returns whether the provider supports signature operations with the public key of `certificate`.
    fn is_public_key_supported(&self, certificate: &[u8]) -> bool;

    /// Returns the certificate at `index` in a chain of concatenated DER certificates.
    ///
    /// # Errors
    ///
    /// Returns [`CryptoError::NotFound`](crate::crypto::error::CryptoError::NotFound) if `index` is out of range.
    fn certificate_from_chain(&self, chain: &[u8], index: usize) -> Result<Vec<u8>>;

    /// Parses a `YYYYMMDDhhmmssZ` UTC string.
    fn parse_date_time(&self, date_time: &str) -> Result<X509DateTime>;

    /// Compares two provider date and time values.
    fn compare_date_time(&self, first: &X509DateTime, second: &X509DateTime) -> Result<Ordering>;

    /// Reads the ASN.1 tag at the start of `data` and checks that it matches `tag`.
    ///
    /// Returns the number of tag and length bytes, followed by the content length.
    ///
    /// # Errors
    ///
    /// Returns [`CryptoError::NotFound`](crate::crypto::error::CryptoError::NotFound) if the tag does not match.
    fn asn1_get_tag(&self, data: &[u8], tag: u32) -> Result<(usize, usize)>;
}
/// One-shot convenience methods for [`Signature`].
pub trait SignatureExt {
    /// Signs `data` with a signer created for `algorithm` and `key`.
    fn sign(&self, algorithm: SignatureAlgorithm, key: SigningKey<'_>, data: &[u8]) -> Result<Vec<u8>>;

    /// Verifies `signature` over `data` with a verifier created for `algorithm` and `certificate`.
    fn verify(
        &self,
        algorithm: SignatureAlgorithm,
        certificate: &[u8],
        data: &[u8],
        signature: &[u8],
    ) -> Result<VerifiedSignature>;
}

impl<T: Signature + ?Sized> SignatureExt for T {
    fn sign(&self, algorithm: SignatureAlgorithm, key: SigningKey<'_>, data: &[u8]) -> Result<Vec<u8>> {
        self.new_signer(algorithm, key)?.sign(data)
    }

    fn verify(
        &self,
        algorithm: SignatureAlgorithm,
        certificate: &[u8],
        data: &[u8],
        signature: &[u8],
    ) -> Result<VerifiedSignature> {
        self.new_verifier(algorithm, certificate)?.verify(data, signature)
    }
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
mod tests {
    use alloc::vec;

    use super::*;
    use crate::crypto::error::CryptoError;

    #[test]
    fn test_signature_signing_key_builder() {
        let others: &[&[u8]] = &[b"ca"];
        let key = SigningKey::new(b"pem").with_password("pw").with_certificates(b"cert", others);
        assert_eq!(key.private_key, b"pem");
        assert_eq!(key.password, Some("pw"));
        assert_eq!(key.certificate, b"cert");
        assert_eq!(key.other_certificates, others);
    }

    #[test]
    fn test_signature_ext_uses_configured_handles() {
        let mut signature = MockSignature::new();
        signature
            .expect_new_signer()
            .withf(|alg, key| *alg == SignatureAlgorithm::Pkcs7 && key.private_key == b"pem")
            .returning(|_, _| {
                let mut signer = MockSigner::new();
                signer.expect_sign().withf(|data| data == b"data").returning(|_| Ok(vec![7]));
                Ok(Box::new(signer))
            });
        signature
            .expect_new_verifier()
            .withf(|alg, cert| *alg == SignatureAlgorithm::Cms && cert == b"root")
            .returning(|_, _| {
                let mut verifier = MockVerifier::new();
                verifier
                    .expect_verify()
                    .withf(|data, sig| data == b"data" && sig == [7])
                    .returning(|_, _| Ok(VerifiedSignature::new(vec![vec![1]])));
                Ok(Box::new(verifier))
            });

        let signed = signature.sign(SignatureAlgorithm::Pkcs7, SigningKey::new(b"pem"), b"data").unwrap();
        let verified = signature.verify(SignatureAlgorithm::Cms, b"root", b"data", &signed).unwrap();
        assert_eq!(verified.signer_chain, vec![vec![1]]);
    }

    #[test]
    fn test_signature_ext_propagates_errors() {
        let mut signature = MockSignature::new();
        signature.expect_new_verifier().returning(|_, _| Err(CryptoError::Unsupported));
        assert_eq!(
            signature.verify(SignatureAlgorithm::Authenticode, b"root", b"hash", b"sig"),
            Err(CryptoError::Unsupported)
        );
    }
}
