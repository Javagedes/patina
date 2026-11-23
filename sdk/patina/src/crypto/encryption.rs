//! Encryption service.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use alloc::{boxed::Box, vec::Vec};

use crate::crypto::{error::Result, hash::HashAlgorithm};

#[cfg(any(test, feature = "mockall"))]
use mockall::automock;

/// AES block size in bytes, and the size of an AES-CBC initialization vector.
pub const AES_BLOCK_SIZE: usize = 16;
/// AES-GCM authentication tag size in bytes.
pub const AES_GCM_TAG_SIZE: usize = 16;

/// Content encryption ciphers for PKCS#7 enveloped data.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Pkcs7Cipher {
    /// AES-128 in CBC mode.
    Aes128Cbc,
    /// AES-192 in CBC mode.
    Aes192Cbc,
    /// AES-256 in CBC mode.
    Aes256Cbc,
}

/// Encryption algorithms.
///
/// Every algorithm uses the same [`Cipher::encrypt`] and [`Cipher::decrypt`] calls. The table lists how each
/// algorithm uses the `nonce` and `aad` arguments and which [`CipherKey`] variants it accepts. Arguments an
/// algorithm does not use must be empty.
///
/// | Algorithm | `nonce` | `aad` | Keys |
/// | --- | --- | --- | --- |
/// | [`AesCbc`](Self::AesCbc) | 16-byte IV | - | [`Symmetric`](CipherKey::Symmetric) |
/// | [`AesGcm`](Self::AesGcm) | IV | Additional data | [`Symmetric`](CipherKey::Symmetric) |
/// | [`RsaOaep`](Self::RsaOaep) | Optional PRNG seed (encrypt) | - | [`Certificate`](CipherKey::Certificate), [`PrivateKeyPem`](CipherKey::PrivateKeyPem), [`PrivateKeyDer`](CipherKey::PrivateKeyDer) |
/// | [`Pkcs7Envelope`](Self::Pkcs7Envelope) | - | - | [`Recipients`](CipherKey::Recipients) |
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum CipherAlgorithm {
    /// AES in CBC mode without padding. Data must be a non-empty multiple of [`AES_BLOCK_SIZE`].
    AesCbc,
    /// AES in GCM mode. Ciphertext is the encrypted data followed by a [`AES_GCM_TAG_SIZE`]-byte tag.
    AesGcm,
    /// RSAES-OAEP. `None` selects SHA-1 for both the label hash and MGF1.
    RsaOaep {
        /// The OAEP hash algorithm.
        digest: Option<HashAlgorithm>,
    },
    /// PKCS#7 enveloped data. Encryption only; the output is DER-encoded enveloped data.
    Pkcs7Envelope(Pkcs7Cipher),
}

/// Key material for [`Encryption::new_cipher`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum CipherKey<'a> {
    /// A raw symmetric key. AES keys are 16, 24, or 32 bytes.
    Symmetric(&'a [u8]),
    /// A PEM-encoded private key, decrypted with `password` if provided. Supports encryption and decryption.
    PrivateKeyPem {
        /// The PEM-encoded key.
        pem: &'a [u8],
        /// The key password.
        password: Option<&'a str>,
    },
    /// A DER-encoded private key. Supports decryption only.
    PrivateKeyDer(&'a [u8]),
    /// A DER-encoded X.509 certificate holding the public key. Supports encryption only.
    Certificate(&'a [u8]),
    /// DER-encoded recipient certificates with RSA public keys. Supports encryption only.
    Recipients(&'a [&'a [u8]]),
}

/// A configured cipher.
///
/// Created by [`Encryption::new_cipher`]. The cipher owns a copy of its key, and dropping it releases its provider
/// resources.
#[cfg_attr(any(test, feature = "mockall"), automock)]
pub trait Cipher {
    /// Encrypts `data`.
    ///
    /// # Errors
    ///
    /// - [`CryptoError::InvalidParameter`](crate::crypto::error::CryptoError::InvalidParameter) if `nonce`, `aad`, or `data`
    ///   is invalid for the algorithm.
    /// - [`CryptoError::Unsupported`](crate::crypto::error::CryptoError::Unsupported) if the key cannot encrypt.
    fn encrypt(&self, nonce: &[u8], aad: &[u8], data: &[u8]) -> Result<Vec<u8>>;

    /// Decrypts `data`.
    ///
    /// # Errors
    ///
    /// - [`CryptoError::InvalidParameter`](crate::crypto::error::CryptoError::InvalidParameter) if `nonce`, `aad`, or `data`
    ///   is invalid for the algorithm.
    /// - [`CryptoError::Unsupported`](crate::crypto::error::CryptoError::Unsupported) if the algorithm or key cannot
    ///   decrypt.
    /// - [`CryptoError::VerificationFailed`](crate::crypto::error::CryptoError::VerificationFailed) if an authenticated
    ///   cipher rejects the tag.
    fn decrypt(&self, nonce: &[u8], aad: &[u8], data: &[u8]) -> Result<Vec<u8>>;
}

/// Encryption operations.
///
/// Equivalent to the `Aes*`, `AeadAesGcm*`, `RsaOaep*`, `Pkcs1v2*`, and `Pkcs7Encrypt` functions in `BaseCryptLib`.
/// The algorithm and key are selected once, and the returned [`Cipher`] encrypts and decrypts the same way for every
/// algorithm. Use [`EncryptionExt`] for one-shot operations.
#[cfg_attr(any(test, feature = "mockall"), automock)]
pub trait Encryption {
    /// Creates a cipher for `algorithm` with `key`.
    ///
    /// # Errors
    ///
    /// - [`CryptoError::InvalidParameter`](crate::crypto::error::CryptoError::InvalidParameter) if `key` is the wrong kind or
    ///   size for `algorithm`.
    /// - [`CryptoError::Unsupported`](crate::crypto::error::CryptoError::Unsupported) if the provider does not support
    ///   `algorithm`.
    #[allow(clippy::needless_lifetimes, reason = "mockall requires explicit lifetimes for nested references")]
    fn new_cipher<'a>(&self, algorithm: CipherAlgorithm, key: CipherKey<'a>) -> Result<Box<dyn Cipher>>;
}

/// One-shot convenience methods for [`Encryption`].
pub trait EncryptionExt {
    /// Encrypts `data` with a cipher created for `algorithm` and `key`.
    fn encrypt(
        &self,
        algorithm: CipherAlgorithm,
        key: CipherKey<'_>,
        nonce: &[u8],
        aad: &[u8],
        data: &[u8],
    ) -> Result<Vec<u8>>;

    /// Decrypts `data` with a cipher created for `algorithm` and `key`.
    fn decrypt(
        &self,
        algorithm: CipherAlgorithm,
        key: CipherKey<'_>,
        nonce: &[u8],
        aad: &[u8],
        data: &[u8],
    ) -> Result<Vec<u8>>;
}

impl<T: Encryption + ?Sized> EncryptionExt for T {
    fn encrypt(
        &self,
        algorithm: CipherAlgorithm,
        key: CipherKey<'_>,
        nonce: &[u8],
        aad: &[u8],
        data: &[u8],
    ) -> Result<Vec<u8>> {
        self.new_cipher(algorithm, key)?.encrypt(nonce, aad, data)
    }

    fn decrypt(
        &self,
        algorithm: CipherAlgorithm,
        key: CipherKey<'_>,
        nonce: &[u8],
        aad: &[u8],
        data: &[u8],
    ) -> Result<Vec<u8>> {
        self.new_cipher(algorithm, key)?.decrypt(nonce, aad, data)
    }
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
mod tests {
    use alloc::vec;

    use super::*;
    use crate::crypto::error::CryptoError;

    #[test]
    fn test_encryption_ext_uses_configured_cipher() {
        let mut encryption = MockEncryption::new();
        encryption
            .expect_new_cipher()
            .withf(|algorithm, key| *algorithm == CipherAlgorithm::AesGcm && *key == CipherKey::Symmetric(b"key"))
            .returning(|_, _| {
                let mut cipher = MockCipher::new();
                cipher
                    .expect_encrypt()
                    .withf(|n, a, d| n == b"iv" && a == b"aad" && d == b"data")
                    .returning(|_, _, _| Ok(vec![1]));
                cipher
                    .expect_decrypt()
                    .withf(|n, a, d| n == b"iv" && a == b"aad" && d == b"ct")
                    .returning(|_, _, _| Ok(vec![2]));
                Ok(Box::new(cipher))
            });

        let key = CipherKey::Symmetric(b"key");
        assert_eq!(encryption.encrypt(CipherAlgorithm::AesGcm, key, b"iv", b"aad", b"data"), Ok(vec![1]));
        assert_eq!(encryption.decrypt(CipherAlgorithm::AesGcm, key, b"iv", b"aad", b"ct"), Ok(vec![2]));
    }

    #[test]
    fn test_encryption_ext_propagates_errors() {
        let mut encryption = MockEncryption::new();
        encryption.expect_new_cipher().returning(|_, _| Err(CryptoError::Unsupported));
        let key = CipherKey::Symmetric(b"key");
        assert_eq!(encryption.encrypt(CipherAlgorithm::AesCbc, key, &[], &[], b"data"), Err(CryptoError::Unsupported));
    }
}
