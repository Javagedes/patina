//! [`Hash`] implementation.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use alloc::{boxed::Box, vec, vec::Vec};
use core::ffi::c_void;

use patina::standard::efi;

use super::{ContextBuffer, OneCrypto, ProviderContext, ensure, protocol_fn};
use crate::{
    error::{CryptoError, Result},
    service::hash::{DigestContext, Hash, HashAlgorithm, KdfAlgorithm, MacAlgorithm},
};

type UpdateFn = unsafe extern "efiapi" fn(*mut c_void, *const c_void, usize) -> efi::Boolean;
type FinalFn = unsafe extern "efiapi" fn(*mut c_void, *mut u8) -> efi::Boolean;
type DuplicateFn = unsafe extern "efiapi" fn(*const c_void, *mut c_void) -> efi::Boolean;

/// The provider functions for one hash algorithm.
#[derive(Clone, Copy)]
struct HashFunctions {
    context_size: usize,
    init: unsafe extern "efiapi" fn(*mut c_void) -> efi::Boolean,
    update: UpdateFn,
    finalize: FinalFn,
    duplicate: DuplicateFn,
    digest_size: usize,
}

impl HashFunctions {
    fn new(crypto: &OneCrypto, algorithm: HashAlgorithm) -> Result<Self> {
        macro_rules! functions {
            ($size:ident, $init:ident, $update:ident, $final:ident, $duplicate:ident) => {{
                let context_size = protocol_fn!(crypto, $size);
                Self {
                    // SAFETY: `GetContextSize` has no preconditions.
                    context_size: unsafe { context_size() },
                    init: protocol_fn!(crypto, $init),
                    update: protocol_fn!(crypto, $update),
                    finalize: protocol_fn!(crypto, $final),
                    duplicate: protocol_fn!(crypto, $duplicate),
                    digest_size: algorithm.digest_size(),
                }
            }};
        }
        Ok(match algorithm {
            HashAlgorithm::Sha1 => {
                functions!(sha1_get_context_size, sha1_init, sha1_update, sha1_final, sha1_duplicate)
            }
            HashAlgorithm::Sha256 => {
                functions!(sha256_get_context_size, sha256_init, sha256_update, sha256_final, sha256_duplicate)
            }
            HashAlgorithm::Sha384 => {
                functions!(sha384_get_context_size, sha384_init, sha384_update, sha384_final, sha384_duplicate)
            }
            HashAlgorithm::Sha512 => {
                functions!(sha512_get_context_size, sha512_init, sha512_update, sha512_final, sha512_duplicate)
            }
            _ => return Err(CryptoError::Unsupported),
        })
    }
}

/// A streaming hash in a caller-allocated context.
struct HashContext {
    functions: HashFunctions,
    context: ContextBuffer,
}

impl DigestContext for HashContext {
    fn update(&mut self, data: &[u8]) -> Result<()> {
        // SAFETY: The context was initialized by `Init` and `data` is valid for the call.
        ensure(unsafe { (self.functions.update)(self.context.as_ptr(), data.as_ptr().cast(), data.len()) })
    }

    fn finalize(self: Box<Self>) -> Result<Vec<u8>> {
        let mut digest = vec![0u8; self.functions.digest_size];
        // SAFETY: The context was initialized by `Init` and `digest` holds the algorithm's digest size.
        ensure(unsafe { (self.functions.finalize)(self.context.as_ptr(), digest.as_mut_ptr()) })?;
        Ok(digest)
    }

    fn duplicate(&self) -> Result<Box<dyn DigestContext>> {
        let context = ContextBuffer::new(self.context.len())?;
        // SAFETY: Both buffers hold `GetContextSize` bytes and the source was initialized by `Init`.
        ensure(unsafe { (self.functions.duplicate)(self.context.as_ptr(), context.as_ptr()) })?;
        Ok(Box::new(Self { functions: self.functions, context }))
    }
}

/// The provider functions for one HMAC algorithm.
#[derive(Clone, Copy)]
struct HmacFunctions {
    new: unsafe extern "efiapi" fn() -> *mut c_void,
    free: unsafe extern "efiapi" fn(*mut c_void),
    update: UpdateFn,
    finalize: FinalFn,
    duplicate: DuplicateFn,
    digest_size: usize,
}

impl HmacFunctions {
    fn new(crypto: &OneCrypto, algorithm: HashAlgorithm) -> Result<Self> {
        let digest_size = algorithm.digest_size();
        Ok(match algorithm {
            HashAlgorithm::Sha256 => Self {
                new: protocol_fn!(crypto, hmac_sha256_new),
                free: protocol_fn!(crypto, hmac_sha256_free),
                update: protocol_fn!(crypto, hmac_sha256_update),
                finalize: protocol_fn!(crypto, hmac_sha256_final),
                duplicate: protocol_fn!(crypto, hmac_sha256_duplicate),
                digest_size,
            },
            HashAlgorithm::Sha384 => Self {
                new: protocol_fn!(crypto, hmac_sha384_new),
                free: protocol_fn!(crypto, hmac_sha384_free),
                update: protocol_fn!(crypto, hmac_sha384_update),
                finalize: protocol_fn!(crypto, hmac_sha384_final),
                duplicate: protocol_fn!(crypto, hmac_sha384_duplicate),
                digest_size,
            },
            _ => return Err(CryptoError::Unsupported),
        })
    }

    fn new_context(&self) -> Result<ProviderContext> {
        // SAFETY: `HmacNew` has no preconditions and its result is released by the matching `HmacFree`.
        unsafe { ProviderContext::new((self.new)(), self.free) }
    }
}

/// A streaming HMAC in a provider-allocated context.
struct HmacContext {
    functions: HmacFunctions,
    context: ProviderContext,
}

impl DigestContext for HmacContext {
    fn update(&mut self, data: &[u8]) -> Result<()> {
        // SAFETY: The context was keyed by `HmacSetKey` and `data` is valid for the call.
        ensure(unsafe { (self.functions.update)(self.context.as_ptr(), data.as_ptr().cast(), data.len()) })
    }

    fn finalize(self: Box<Self>) -> Result<Vec<u8>> {
        let mut digest = vec![0u8; self.functions.digest_size];
        // SAFETY: The context was keyed by `HmacSetKey` and `digest` holds the algorithm's digest size.
        ensure(unsafe { (self.functions.finalize)(self.context.as_ptr(), digest.as_mut_ptr()) })?;
        Ok(digest)
    }

    fn duplicate(&self) -> Result<Box<dyn DigestContext>> {
        let context = self.functions.new_context()?;
        // SAFETY: Both contexts were allocated by `HmacNew` for the same algorithm.
        ensure(unsafe { (self.functions.duplicate)(self.context.as_ptr(), context.as_ptr()) })?;
        Ok(Box::new(Self { functions: self.functions, context }))
    }
}

impl Hash for OneCrypto {
    fn new_hash(&self, algorithm: HashAlgorithm) -> Result<Box<dyn DigestContext>> {
        let functions = HashFunctions::new(self, algorithm)?;
        let context = ContextBuffer::new(functions.context_size)?;
        // SAFETY: `context` holds `GetContextSize` bytes.
        ensure(unsafe { (functions.init)(context.as_ptr()) })?;
        Ok(Box::new(HashContext { functions, context }))
    }

    fn new_mac(&self, algorithm: MacAlgorithm, key: &[u8]) -> Result<Box<dyn DigestContext>> {
        let MacAlgorithm::Hmac(algorithm) = algorithm else {
            return Err(CryptoError::Unsupported);
        };
        let functions = HmacFunctions::new(self, algorithm)?;
        let set_key = match algorithm {
            HashAlgorithm::Sha256 => protocol_fn!(self, hmac_sha256_set_key),
            _ => protocol_fn!(self, hmac_sha384_set_key),
        };
        let context = functions.new_context()?;
        // SAFETY: `context` was allocated by `HmacNew` and `key` is valid for the call.
        ensure(unsafe { set_key(context.as_ptr(), key.as_ptr(), key.len()) })?;
        Ok(Box::new(HmacContext { functions, context }))
    }

    fn hash_all(&self, algorithm: HashAlgorithm, data: &[u8]) -> Result<Vec<u8>> {
        let hash_all = match algorithm {
            HashAlgorithm::Sha1 => protocol_fn!(self, sha1_hash_all),
            HashAlgorithm::Sha256 => protocol_fn!(self, sha256_hash_all),
            HashAlgorithm::Sha384 => protocol_fn!(self, sha384_hash_all),
            HashAlgorithm::Sha512 => protocol_fn!(self, sha512_hash_all),
            _ => return Err(CryptoError::Unsupported),
        };
        let mut digest = vec![0u8; algorithm.digest_size()];
        // SAFETY: `data` is valid for the call and `digest` holds the algorithm's digest size.
        ensure(unsafe { hash_all(data.as_ptr().cast(), data.len(), digest.as_mut_ptr()) })?;
        Ok(digest)
    }

    fn mac_all(&self, algorithm: MacAlgorithm, key: &[u8], data: &[u8]) -> Result<Vec<u8>> {
        let MacAlgorithm::Hmac(digest) = algorithm else {
            return Err(CryptoError::Unsupported);
        };
        let mac_all = match digest {
            HashAlgorithm::Sha256 => protocol_fn!(self, hmac_sha256_all),
            HashAlgorithm::Sha384 => protocol_fn!(self, hmac_sha384_all),
            _ => return Err(CryptoError::Unsupported),
        };
        let mut mac = vec![0u8; algorithm.mac_size()];
        // SAFETY: `data` and `key` are valid for the call and `mac` holds the algorithm's MAC size.
        ensure(unsafe { mac_all(data.as_ptr().cast(), data.len(), key.as_ptr(), key.len(), mac.as_mut_ptr()) })?;
        Ok(mac)
    }

    fn derive_key(
        &self,
        algorithm: KdfAlgorithm,
        key: &[u8],
        salt: &[u8],
        info: &[u8],
        output: &mut [u8],
    ) -> Result<()> {
        self.kdf(algorithm, key, salt, info, output)
    }
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
pub(super) mod tests {
    use super::{super::test_support::*, *};

    // A fake SHA-256 whose context is a running byte sum and whose digest repeats that sum.
    extern "efiapi" fn context_size() -> usize {
        8
    }
    extern "efiapi" fn init(context: *mut c_void) -> efi::Boolean {
        // SAFETY: Contexts are 8 bytes.
        unsafe { context.cast::<u64>().write(0) };
        boolean(true)
    }
    extern "efiapi" fn update(context: *mut c_void, data: *const c_void, len: usize) -> efi::Boolean {
        // SAFETY: Contexts are 8 bytes and `data` is readable for `len` bytes.
        unsafe { *context.cast::<u64>() += input(data.cast(), len).iter().map(|&b| u64::from(b)).sum::<u64>() };
        boolean(true)
    }
    extern "efiapi" fn finalize(context: *mut c_void, digest: *mut u8) -> efi::Boolean {
        // SAFETY: Contexts are 8 bytes and the digest is 32 bytes.
        unsafe { digest.write_bytes(*context.cast::<u64>() as u8, 32) };
        boolean(true)
    }
    extern "efiapi" fn duplicate(context: *const c_void, new: *mut c_void) -> efi::Boolean {
        // SAFETY: Contexts are 8 bytes.
        unsafe { new.cast::<u64>().write(*context.cast::<u64>()) };
        boolean(true)
    }
    // A fake HMAC-SHA256 that uses a boxed u64 context seeded by the key length.
    extern "efiapi" fn hmac_new() -> *mut c_void {
        Box::into_raw(Box::new(0u64)).cast()
    }
    extern "efiapi" fn hmac_free(context: *mut c_void) {
        // SAFETY: Contexts come from `hmac_new`.
        drop(unsafe { Box::from_raw(context.cast::<u64>()) });
    }
    extern "efiapi" fn hmac_set_key(context: *mut c_void, _key: *const u8, len: usize) -> efi::Boolean {
        // SAFETY: Contexts come from `hmac_new`.
        unsafe { context.cast::<u64>().write(len as u64) };
        boolean(true)
    }
    extern "efiapi" fn hash_all(data: *const c_void, len: usize, digest: *mut u8) -> efi::Boolean {
        // SAFETY: `data` is readable for `len` bytes.
        let sum = unsafe { input(data.cast(), len) }.iter().map(|&b| u64::from(b)).sum::<u64>();
        // SAFETY: The digest is 32 bytes.
        unsafe { digest.write_bytes(sum as u8, 32) };
        boolean(true)
    }
    extern "efiapi" fn hmac_all(
        data: *const c_void,
        len: usize,
        _key: *const u8,
        key_len: usize,
        mac: *mut u8,
    ) -> efi::Boolean {
        // SAFETY: `data` is readable for `len` bytes.
        let sum = unsafe { input(data.cast(), len) }.iter().map(|&b| u64::from(b)).sum::<u64>();
        // SAFETY: The MAC is 32 bytes.
        unsafe { mac.write_bytes((sum + key_len as u64) as u8, 32) };
        boolean(true)
    }
    fn sha256_protocol() -> OneCrypto {
        crypto(with_sha256(protocol()))
    }

    /// Adds the fake SHA-256 and HMAC-SHA256 functions to `base`.
    pub(in crate::one_crypto) fn with_sha256(base: OneCryptoProtocol) -> OneCryptoProtocol {
        OneCryptoProtocol {
            sha256_get_context_size: Some(context_size),
            sha256_init: Some(init),
            sha256_update: Some(update),
            sha256_final: Some(finalize),
            sha256_duplicate: Some(duplicate),
            sha256_hash_all: Some(hash_all),
            hmac_sha256_all: Some(hmac_all),
            hmac_sha256_new: Some(hmac_new),
            hmac_sha256_free: Some(hmac_free),
            hmac_sha256_set_key: Some(hmac_set_key),
            hmac_sha256_update: Some(update),
            hmac_sha256_final: Some(finalize),
            hmac_sha256_duplicate: Some(duplicate),
            ..base
        }
    }

    use super::super::protocol::OneCryptoProtocol;

    #[test]
    fn test_one_crypto_digest_streams_and_duplicates() {
        let crypto = sha256_protocol();
        let mut hash = crypto.new_hash(HashAlgorithm::Sha256).expect("hash");
        hash.update(&[1, 2]).expect("update");
        let copy = hash.duplicate().expect("duplicate");
        hash.update(&[3]).expect("update");
        assert_eq!(hash.finalize(), Ok(vec![6; 32]));
        assert_eq!(copy.finalize(), Ok(vec![3; 32]));
        assert_eq!(crypto.hash_all(HashAlgorithm::Sha256, &[1, 2, 3]), Ok(vec![6; 32]));
    }

    #[test]
    fn test_one_crypto_digest_hmac_streams_and_duplicates() {
        let crypto = sha256_protocol();
        let mut hmac = crypto.new_mac(MacAlgorithm::Hmac(HashAlgorithm::Sha256), &[0; 4]).expect("hmac");
        hmac.update(&[1]).expect("update");
        let copy = hmac.duplicate().expect("duplicate");
        hmac.update(&[1]).expect("update");
        assert_eq!(hmac.finalize(), Ok(vec![6; 32]));
        assert_eq!(copy.finalize(), Ok(vec![5; 32]));
        assert_eq!(crypto.mac_all(MacAlgorithm::Hmac(HashAlgorithm::Sha256), &[0; 4], &[2]), Ok(vec![6; 32]));
    }

    #[test]
    fn test_one_crypto_digest_reports_unsupported_algorithms() {
        let crypto = sha256_protocol();
        for algorithm in [HashAlgorithm::Sha1, HashAlgorithm::Sha384, HashAlgorithm::Sha512] {
            assert_eq!(crypto.new_hash(algorithm).err(), Some(CryptoError::Unsupported));
            assert_eq!(crypto.hash_all(algorithm, &[]), Err(CryptoError::Unsupported));
        }
        for algorithm in [HashAlgorithm::Sha1, HashAlgorithm::Sha384, HashAlgorithm::Sha512] {
            assert_eq!(crypto.new_mac(MacAlgorithm::Hmac(algorithm), &[]).err(), Some(CryptoError::Unsupported));
            assert_eq!(crypto.mac_all(MacAlgorithm::Hmac(algorithm), &[], &[]), Err(CryptoError::Unsupported));
        }
    }
}
