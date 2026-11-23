//! Hash service: message digests, message authentication codes, and key derivation.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use alloc::{boxed::Box, vec::Vec};

use crate::crypto::error::Result;

#[cfg(any(test, feature = "mockall"))]
use mockall::automock;

/// Hash algorithms supported by cryptographic services.
///
/// Services document which algorithms they accept. Passing an algorithm a service does not support returns
/// [`CryptoError::Unsupported`](crate::crypto::error::CryptoError::Unsupported).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum HashAlgorithm {
    /// SHA-1. Only for verifying legacy data.
    Sha1,
    /// SHA-256.
    Sha256,
    /// SHA-384.
    Sha384,
    /// SHA-512.
    Sha512,
}

impl HashAlgorithm {
    /// Returns the digest size of this algorithm in bytes.
    pub const fn digest_size(self) -> usize {
        match self {
            Self::Sha1 => 20,
            Self::Sha256 => 32,
            Self::Sha384 => 48,
            Self::Sha512 => 64,
        }
    }
}

/// Message authentication code algorithms.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum MacAlgorithm {
    /// HMAC with the given hash. `BaseCryptLib` supports SHA-256 and SHA-384.
    Hmac(HashAlgorithm),
}

impl MacAlgorithm {
    /// Returns the MAC size of this algorithm in bytes.
    pub const fn mac_size(self) -> usize {
        match self {
            Self::Hmac(digest) => digest.digest_size(),
        }
    }
}

/// Key derivation algorithms.
///
/// Every algorithm uses the same [`Hash::derive_key`] call. Inputs an algorithm does not use must be empty.
///
/// | Algorithm | `key` | `salt` | `info` | `output` |
/// | --- | --- | --- | --- | --- |
/// | [`Pbkdf2`](Self::Pbkdf2) | Password | Salt | - | Derived key |
/// | [`Hkdf`](Self::Hkdf) | Input key material | Salt | Info | Derived key |
/// | [`HkdfExtract`](Self::HkdfExtract) | Input key material | Salt | - | Pseudorandom key, digest size |
/// | [`HkdfExpand`](Self::HkdfExpand) | Pseudorandom key | - | Info | Derived key |
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum KdfAlgorithm {
    /// PBKDF2 with HMAC over `digest`. `BaseCryptLib` supports SHA-1 and SHA-256.
    Pbkdf2 {
        /// The HMAC hash algorithm.
        digest: HashAlgorithm,
        /// The iteration count.
        iterations: usize,
    },
    /// HKDF extract and expand. `BaseCryptLib` supports SHA-256 and SHA-384.
    Hkdf {
        /// The HMAC hash algorithm.
        digest: HashAlgorithm,
    },
    /// The HKDF extract step only.
    HkdfExtract {
        /// The HMAC hash algorithm.
        digest: HashAlgorithm,
    },
    /// The HKDF expand step only.
    HkdfExpand {
        /// The HMAC hash algorithm.
        digest: HashAlgorithm,
    },
}

/// An in-progress hash or MAC computation.
///
/// Dropping the context releases its provider resources.
#[cfg_attr(any(test, feature = "mockall"), automock)]
pub trait DigestContext {
    /// Adds `data` to the digest.
    fn update(&mut self, data: &[u8]) -> Result<()>;

    /// Completes the computation and returns the digest.
    fn finalize(self: Box<Self>) -> Result<Vec<u8>>;

    /// Returns an independent copy of the current state.
    fn duplicate(&self) -> Result<Box<dyn DigestContext>>;
}

/// Hash-based operations: digests, MACs, and key derivation.
///
/// Equivalent to the `Sha*`, `HashAllByGuid`, `HmacSha*`, `Pkcs5HashPassword`, and `Hkdf*` functions in
/// `BaseCryptLib`. The algorithm (and key, for MACs) is selected through an enum, so consumers hash the same way
/// regardless of the algorithm. Use [`new_hash`](Self::new_hash) and [`new_mac`](Self::new_mac) to stream data, or
/// [`hash_all`](Self::hash_all) and [`mac_all`](Self::mac_all) when all data is available at once.
#[cfg_attr(any(test, feature = "mockall"), automock)]
pub trait Hash {
    /// Starts a streaming hash computation with `algorithm`.
    ///
    /// # Errors
    ///
    /// Returns [`CryptoError::Unsupported`](crate::crypto::error::CryptoError::Unsupported) if the provider does not support `algorithm`.
    fn new_hash(&self, algorithm: HashAlgorithm) -> Result<Box<dyn DigestContext>>;

    /// Starts a streaming MAC computation with `algorithm` keyed with `key`.
    ///
    /// # Errors
    ///
    /// Returns [`CryptoError::Unsupported`](crate::crypto::error::CryptoError::Unsupported) if the provider does not support `algorithm`.
    fn new_mac(&self, algorithm: MacAlgorithm, key: &[u8]) -> Result<Box<dyn DigestContext>>;

    /// Returns the `algorithm` digest of `data`.
    ///
    /// # Errors
    ///
    /// Returns [`CryptoError::Unsupported`](crate::crypto::error::CryptoError::Unsupported) if the provider does not support `algorithm`.
    fn hash_all(&self, algorithm: HashAlgorithm, data: &[u8]) -> Result<Vec<u8>>;

    /// Returns the `algorithm` MAC of `data` keyed with `key`.
    ///
    /// # Errors
    ///
    /// Returns [`CryptoError::Unsupported`](crate::crypto::error::CryptoError::Unsupported) if the provider does not support `algorithm`.
    fn mac_all(&self, algorithm: MacAlgorithm, key: &[u8], data: &[u8]) -> Result<Vec<u8>>;

    /// Derives key material with `algorithm` into `output`.
    ///
    /// # Errors
    ///
    /// - [`CryptoError::Unsupported`](crate::crypto::error::CryptoError::Unsupported) if the provider does not support `algorithm`.
    /// - [`CryptoError::InvalidParameter`](crate::crypto::error::CryptoError::InvalidParameter) if an input the algorithm does not use is non-empty, or `output` has the
    ///   wrong size.
    fn derive_key(
        &self,
        algorithm: KdfAlgorithm,
        key: &[u8],
        salt: &[u8],
        info: &[u8],
        output: &mut [u8],
    ) -> Result<()>;
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
mod tests {
    use super::*;
    use alloc::vec;
    use mockall::predicate::eq;

    #[test]
    fn test_hash_algorithm_sizes() {
        assert_eq!(HashAlgorithm::Sha1.digest_size(), 20);
        assert_eq!(HashAlgorithm::Sha256.digest_size(), 32);
        assert_eq!(HashAlgorithm::Sha384.digest_size(), 48);
        assert_eq!(HashAlgorithm::Sha512.digest_size(), 64);
        assert_eq!(MacAlgorithm::Hmac(HashAlgorithm::Sha384).mac_size(), 48);
    }

    #[test]
    fn test_hash_digest_context_streams_through_trait_object() {
        let mut context = MockDigestContext::new();
        context.expect_update().with(eq(b"data".as_slice())).times(1).returning(|_| Ok(()));
        context.expect_finalize().times(1).returning(|| Ok(vec![1, 2, 3]));
        let mut context: Box<dyn DigestContext> = Box::new(context);
        context.update(b"data").unwrap();
        assert_eq!(context.finalize().unwrap(), vec![1, 2, 3]);
    }
}
