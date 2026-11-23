//! [`Encryption`] implementation.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use alloc::{boxed::Box, vec::Vec};

use super::{OneCrypto, aes::AesCbcKey, rsa::RsaKey};
use crate::{
    error::{CryptoError, Result},
    service::{
        encryption::{Cipher, CipherAlgorithm, CipherKey, Encryption, Pkcs7Cipher},
        hash::HashAlgorithm,
    },
};

/// Returns [`CryptoError::InvalidParameter`] unless every argument is empty.
fn ensure_unused(arguments: &[&[u8]]) -> Result<()> {
    if arguments.iter().all(|argument| argument.is_empty()) { Ok(()) } else { Err(CryptoError::InvalidParameter) }
}

/// The configured algorithm and owned key material.
enum CipherState {
    AesCbc(AesCbcKey),
    AesGcm(Vec<u8>),
    /// An RSA key context. `private` keys can also decrypt.
    RsaOaep {
        key: RsaKey,
        digest: Option<HashAlgorithm>,
        private: bool,
    },
    /// A DER-encoded private key for `Pkcs1v2Decrypt`, which only supports SHA-1.
    RsaOaepDer(Vec<u8>),
    Pkcs7Envelope {
        recipients: Vec<Vec<u8>>,
        cipher: Pkcs7Cipher,
    },
}

/// A [`Cipher`] backed by the OneCrypto protocol.
struct OneCryptoCipher {
    crypto: OneCrypto,
    state: CipherState,
}

impl Cipher for OneCryptoCipher {
    fn encrypt(&self, nonce: &[u8], aad: &[u8], data: &[u8]) -> Result<Vec<u8>> {
        match &self.state {
            CipherState::AesCbc(key) => {
                ensure_unused(&[aad])?;
                key.encrypt(data, nonce)
            }
            CipherState::AesGcm(key) => self.crypto.aes_gcm_encrypt(key, nonce, aad, data),
            CipherState::RsaOaep { key, digest, .. } => {
                ensure_unused(&[aad])?;
                key.oaep_encrypt(data, nonce, *digest)
            }
            CipherState::RsaOaepDer(_) => Err(CryptoError::Unsupported),
            CipherState::Pkcs7Envelope { recipients, cipher } => {
                ensure_unused(&[nonce, aad])?;
                let recipients = recipients.iter().map(Vec::as_slice).collect::<Vec<_>>();
                self.crypto.pkcs7_encrypt(&recipients, data, *cipher)
            }
        }
    }

    fn decrypt(&self, nonce: &[u8], aad: &[u8], data: &[u8]) -> Result<Vec<u8>> {
        match &self.state {
            CipherState::AesCbc(key) => {
                ensure_unused(&[aad])?;
                key.decrypt(data, nonce)
            }
            CipherState::AesGcm(key) => self.crypto.aes_gcm_decrypt(key, nonce, aad, data),
            CipherState::RsaOaep { key, digest, private: true } => {
                ensure_unused(&[nonce, aad])?;
                key.oaep_decrypt(data, *digest)
            }
            CipherState::RsaOaepDer(key) => {
                ensure_unused(&[nonce, aad])?;
                self.crypto.pkcs1v2_decrypt(key, data)
            }
            CipherState::RsaOaep { private: false, .. } | CipherState::Pkcs7Envelope { .. } => {
                Err(CryptoError::Unsupported)
            }
        }
    }
}

impl Encryption for OneCrypto {
    fn new_cipher(&self, algorithm: CipherAlgorithm, key: CipherKey<'_>) -> Result<Box<dyn Cipher>> {
        let state = match (algorithm, key) {
            (CipherAlgorithm::AesCbc, CipherKey::Symmetric(key)) => CipherState::AesCbc(self.aes_cbc_key(key)?),
            (CipherAlgorithm::AesGcm, CipherKey::Symmetric(key)) => {
                if !matches!(key.len(), 16 | 24 | 32) {
                    return Err(CryptoError::InvalidParameter);
                }
                CipherState::AesGcm(key.to_vec())
            }
            (CipherAlgorithm::RsaOaep { digest }, CipherKey::Certificate(certificate)) => {
                CipherState::RsaOaep { key: self.rsa_public_key_from_x509(certificate)?, digest, private: false }
            }
            (CipherAlgorithm::RsaOaep { digest }, CipherKey::PrivateKeyPem { pem, password }) => {
                CipherState::RsaOaep { key: self.rsa_private_key_from_pem(pem, password)?, digest, private: true }
            }
            (CipherAlgorithm::RsaOaep { digest: None }, CipherKey::PrivateKeyDer(key)) => {
                CipherState::RsaOaepDer(key.to_vec())
            }
            (CipherAlgorithm::RsaOaep { digest: Some(_) }, CipherKey::PrivateKeyDer(_)) => {
                return Err(CryptoError::Unsupported);
            }
            (CipherAlgorithm::Pkcs7Envelope(cipher), CipherKey::Recipients(recipients)) => {
                CipherState::Pkcs7Envelope { recipients: recipients.iter().map(|r| r.to_vec()).collect(), cipher }
            }
            _ => return Err(CryptoError::InvalidParameter),
        };
        Ok(Box::new(OneCryptoCipher { crypto: *self, state }))
    }
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
mod tests {
    use alloc::vec;

    use super::{
        super::{aes::tests::aes, pkcs7::tests::pkcs7, rsa::tests::rsa_protocol, test_support::*},
        *,
    };
    use crate::service::encryption::{AES_BLOCK_SIZE, AES_GCM_TAG_SIZE, EncryptionExt};

    #[test]
    fn test_one_crypto_cipher_aes_cbc() {
        let crypto = aes();
        let cipher = crypto.new_cipher(CipherAlgorithm::AesCbc, CipherKey::Symmetric(&[0x5a; 16])).expect("cipher");
        let iv = [0u8; AES_BLOCK_SIZE];
        let ciphertext = cipher.encrypt(&iv, &[], &[1; 16]).expect("encrypt");
        assert_eq!(ciphertext, vec![1 ^ 0x5a; 16]);
        assert_eq!(cipher.decrypt(&iv, &[], &ciphertext), Ok(vec![1; 16]));
        assert_eq!(cipher.encrypt(&iv, &[1], &[1; 16]), Err(CryptoError::InvalidParameter));
        assert_eq!(cipher.decrypt(&iv, &[1], &[1; 16]), Err(CryptoError::InvalidParameter));
        assert_eq!(cipher.encrypt(&[], &[], &[1; 16]), Err(CryptoError::InvalidParameter));
    }

    #[test]
    fn test_one_crypto_cipher_aes_gcm() {
        let crypto = aes();
        let key = CipherKey::Symmetric(&[3; 32]);
        let ciphertext = crypto.encrypt(CipherAlgorithm::AesGcm, key, &[0; 12], b"aad", &[1, 2]).expect("encrypt");
        assert_eq!(ciphertext.len(), 2 + AES_GCM_TAG_SIZE);
        assert_eq!(crypto.decrypt(CipherAlgorithm::AesGcm, key, &[0; 12], b"aad", &ciphertext), Ok(vec![1, 2]));
        assert_eq!(
            crypto.new_cipher(CipherAlgorithm::AesGcm, CipherKey::Symmetric(&[0; 15])).err(),
            Some(CryptoError::InvalidParameter)
        );
    }

    #[test]
    fn test_one_crypto_cipher_rsa_oaep() {
        let crypto = crypto_with_frees(rsa_protocol(), 4);
        let sha256 = CipherAlgorithm::RsaOaep { digest: Some(HashAlgorithm::Sha256) };
        let public = crypto.new_cipher(sha256, CipherKey::Certificate(&[0])).expect("public");
        assert_eq!(public.encrypt(&[9], &[], &[1]), Ok(vec![1, 32]));
        assert_eq!(public.encrypt(&[], &[1], &[1]), Err(CryptoError::InvalidParameter));
        assert_eq!(public.decrypt(&[], &[], &[1]), Err(CryptoError::Unsupported));

        let private = crypto.new_cipher(sha256, CipherKey::PrivateKeyPem { pem: &[0], password: None }).expect("pem");
        assert_eq!(private.encrypt(&[], &[], &[2]), Ok(vec![2, 32]));
        assert_eq!(private.decrypt(&[], &[], &[3]), Ok(vec![3, 32]));
        assert_eq!(private.decrypt(&[1], &[], &[3]), Err(CryptoError::InvalidParameter));

        let sha1 = CipherAlgorithm::RsaOaep { digest: None };
        let der = crypto.new_cipher(sha1, CipherKey::PrivateKeyDer(&[0])).expect("der");
        assert_eq!(der.decrypt(&[], &[], &[4]), Ok(vec![4, 0]));
        assert_eq!(der.decrypt(&[], &[1], &[4]), Err(CryptoError::InvalidParameter));
        assert_eq!(der.encrypt(&[], &[], &[4]), Err(CryptoError::Unsupported));
        assert_eq!(crypto.new_cipher(sha256, CipherKey::PrivateKeyDer(&[0])).err(), Some(CryptoError::Unsupported));
    }

    #[test]
    fn test_one_crypto_cipher_pkcs7_envelope() {
        let crypto = crypto_with_frees(pkcs7(), 1);
        let algorithm = CipherAlgorithm::Pkcs7Envelope(Pkcs7Cipher::Aes256Cbc);
        let cipher = crypto.new_cipher(algorithm, CipherKey::Recipients(&[])).expect("cipher");
        assert_eq!(cipher.encrypt(&[], &[], &[1]).map(|output| output[..2].to_vec()), Ok(vec![1, 1]));
        assert_eq!(cipher.encrypt(&[1], &[], &[1]), Err(CryptoError::InvalidParameter));
        assert_eq!(cipher.decrypt(&[], &[], &[1]), Err(CryptoError::Unsupported));
        let cipher = crypto.new_cipher(algorithm, CipherKey::Recipients(&[&[2]])).expect("cipher");
        assert_eq!(cipher.encrypt(&[], &[], &[1]), Err(CryptoError::Unsupported));
    }

    #[test]
    fn test_one_crypto_cipher_rejects_mismatched_keys() {
        let crypto = crypto(protocol());
        let mismatched = [
            (CipherAlgorithm::AesCbc, CipherKey::Certificate(&[0])),
            (CipherAlgorithm::AesGcm, CipherKey::PrivateKeyDer(&[0])),
            (CipherAlgorithm::RsaOaep { digest: None }, CipherKey::Symmetric(&[0; 16])),
            (CipherAlgorithm::Pkcs7Envelope(Pkcs7Cipher::Aes128Cbc), CipherKey::Symmetric(&[0; 16])),
        ];
        for (algorithm, key) in mismatched {
            assert_eq!(crypto.new_cipher(algorithm, key).err(), Some(CryptoError::InvalidParameter));
        }
    }
}
