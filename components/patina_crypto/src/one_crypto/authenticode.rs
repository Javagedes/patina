//! The Authenticode verification used by the signature service.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use alloc::{boxed::Box, vec::Vec};
use core::ffi::c_void;

use patina::standard::efi;

use super::{
    OneCrypto, ensure_or, parse_cert_stack,
    protocol::{
        HASH_ALGORITHM_SHA1_GUID, HASH_ALGORITHM_SHA256_GUID, HASH_ALGORITHM_SHA384_GUID, HASH_ALGORITHM_SHA512_GUID,
    },
    protocol_fn, protocol_v2_fn, status_to_result,
};
use crate::{
    error::{CryptoError, Result},
    service::{hash::HashAlgorithm, signature::TrustAnchorCache},
};

/// Calls `GetTrustAnchorX509FromAuthData()` with an optional cache handle.
fn find_trust_anchor(
    crypto: &OneCrypto,
    cache: *mut *mut c_void,
    tbs_certificate_hash: &[u8],
    signature: &[u8],
) -> Result<Vec<u8>> {
    let find = protocol_v2_fn!(crypto, get_trust_anchor_x509_from_auth_data);
    let mut certificate = core::ptr::null_mut();
    let mut certificate_size = 0;
    // SAFETY: The inputs are valid for the call and `cache` is null or points to a provider cache handle.
    status_to_result(unsafe {
        find(
            cache,
            tbs_certificate_hash.as_ptr(),
            tbs_certificate_hash.len(),
            signature.as_ptr(),
            signature.len(),
            &mut certificate,
            &mut certificate_size,
        )
    })?;
    // SAFETY: On success, `certificate` is a pool allocation of `certificate_size` bytes owned by the caller.
    let certificate = unsafe { crypto.take_pool(certificate, certificate_size) };
    if certificate.is_empty() {
        return Err(CryptoError::NotFound);
    }
    Ok(certificate)
}

/// A trust anchor cache handle owned by the provider and released with `FreeTrustAnchorX509Cache()`.
struct OneCryptoTrustAnchorCache {
    crypto: OneCrypto,
    handle: *mut c_void,
    free: unsafe extern "efiapi" fn(*mut c_void),
}

impl TrustAnchorCache for OneCryptoTrustAnchorCache {
    fn trust_anchor(&mut self, tbs_certificate_hash: &[u8], signature: &[u8]) -> Result<Vec<u8>> {
        find_trust_anchor(&self.crypto, &mut self.handle, tbs_certificate_hash, signature)
    }
}

impl Drop for OneCryptoTrustAnchorCache {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            // SAFETY: `handle` was allocated by `GetTrustAnchorX509FromAuthData()` and is released exactly once.
            unsafe { (self.free)(self.handle) }
        }
    }
}

impl OneCrypto {
    /// Verifies an Authenticode `signature` over `image_hash` against `trusted_certificate`.
    ///
    /// Returns the verified certificate chain when the provider implements `AuthenticodeVerifyEx()`, or an empty
    /// chain when it only implements `AuthenticodeVerify()`.
    pub(super) fn authenticode_verify(
        &self,
        signature: &[u8],
        trusted_certificate: &[u8],
        image_hash: &[u8],
    ) -> Result<Vec<Vec<u8>>> {
        let Some(verify) = self.protocol_v2().and_then(|v2| v2.authenticode_verify_ex) else {
            let verify = protocol_fn!(self, authenticode_verify);
            // SAFETY: The inputs are valid for the call.
            let result = unsafe {
                verify(
                    signature.as_ptr(),
                    signature.len(),
                    trusted_certificate.as_ptr(),
                    trusted_certificate.len(),
                    image_hash.as_ptr(),
                    image_hash.len(),
                )
            };
            return ensure_or(result, CryptoError::VerificationFailed).map(|_| Vec::new());
        };
        let mut chain = core::ptr::null_mut();
        let mut chain_size = 0;
        // SAFETY: The inputs are valid for the call.
        status_to_result(unsafe {
            verify(
                signature.as_ptr(),
                signature.len(),
                trusted_certificate.as_ptr(),
                trusted_certificate.len(),
                image_hash.as_ptr(),
                image_hash.len(),
                &mut chain,
                &mut chain_size,
            )
        })?;
        // SAFETY: On success, `chain` is a pool allocation of `chain_size` bytes owned by the caller.
        parse_cert_stack(&unsafe { self.take_pool(chain, chain_size) })
    }
}

impl OneCrypto {
    pub(super) fn authenticode_hash_algorithm(&self, signature: &[u8]) -> Result<HashAlgorithm> {
        let get_algorithm = protocol_v2_fn!(self, get_authenticode_hash_algorithm);
        let mut guid = efi::Guid::from_bytes(&[0; 16]);
        // SAFETY: `signature` is valid for the call and `guid` is writable.
        status_to_result(unsafe { get_algorithm(signature.as_ptr(), signature.len(), &mut guid) })?;
        [
            (HASH_ALGORITHM_SHA1_GUID, HashAlgorithm::Sha1),
            (HASH_ALGORITHM_SHA256_GUID, HashAlgorithm::Sha256),
            (HASH_ALGORITHM_SHA384_GUID, HashAlgorithm::Sha384),
            (HASH_ALGORITHM_SHA512_GUID, HashAlgorithm::Sha512),
        ]
        .into_iter()
        .find_map(|(id, algorithm)| (id == guid).then_some(algorithm))
        .ok_or(CryptoError::Unsupported)
    }

    pub(super) fn trust_anchor(&self, tbs_certificate_hash: &[u8], signature: &[u8]) -> Result<Vec<u8>> {
        find_trust_anchor(self, core::ptr::null_mut(), tbs_certificate_hash, signature)
    }

    pub(super) fn new_trust_anchor_cache(&self) -> Result<Box<dyn TrustAnchorCache>> {
        protocol_v2_fn!(self, get_trust_anchor_x509_from_auth_data);
        let free = protocol_v2_fn!(self, free_trust_anchor_x509_cache);
        Ok(Box::new(OneCryptoTrustAnchorCache { crypto: *self, handle: core::ptr::null_mut(), free }))
    }

    pub(super) fn verify_timestamp(&self, signature: &[u8], tsa_certificate: &[u8]) -> Result<efi::Time> {
        let verify = protocol_fn!(self, image_timestamp_verify);
        let mut signing_time = efi::Time::default();
        // SAFETY: The inputs are valid for the call and `signing_time` is writable.
        let result = unsafe {
            verify(
                signature.as_ptr(),
                signature.len(),
                tsa_certificate.as_ptr(),
                tsa_certificate.len(),
                &mut signing_time,
            )
        };
        ensure_or(result, CryptoError::VerificationFailed)?;
        Ok(signing_time)
    }
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
pub(super) mod tests {
    use alloc::{boxed::Box, vec};
    use core::sync::atomic::{AtomicUsize, Ordering};

    use super::{
        super::{
            protocol::{OneCryptoProtocol, OneCryptoProtocolV2, OneCryptoProtocolV2Extension},
            test_support::*,
        },
        *,
    };
    use crate::service::signature::Signature;

    extern "efiapi" fn verify(
        signature: *const u8,
        signature_len: usize,
        _cert: *const u8,
        _cert_len: usize,
        hash: *const u8,
        hash_len: usize,
    ) -> efi::Boolean {
        // SAFETY: The inputs are readable for their lengths.
        boolean(unsafe { input(signature, signature_len) == input(hash, hash_len) })
    }
    #[allow(clippy::too_many_arguments)]
    extern "efiapi" fn verify_ex(
        signature: *const u8,
        signature_len: usize,
        cert: *const u8,
        cert_len: usize,
        hash: *const u8,
        hash_len: usize,
        chain: *mut *mut u8,
        chain_len: *mut usize,
    ) -> efi::Status {
        if hash_len == 0 {
            return efi::Status::INVALID_PARAMETER;
        }
        if !bool::from(verify(signature, signature_len, cert, cert_len, hash, hash_len)) {
            return efi::Status::SECURITY_VIOLATION;
        }
        // SAFETY: The outputs are writable.
        unsafe {
            chain.write(pool_buffer(&[2, 1, 0, 0, 0, 5, 1, 0, 0, 0, 6]));
            chain_len.write(11);
        }
        efi::Status::SUCCESS
    }
    extern "efiapi" fn hash_algorithm(signature: *const u8, len: usize, guid: *mut efi::Guid) -> efi::Status {
        // SAFETY: `signature` is readable for `len` bytes and `guid` is writable.
        unsafe {
            match input(signature, len) {
                [1] => guid.write(*HASH_ALGORITHM_SHA1_GUID.as_efi_guid()),
                [2] => guid.write(*HASH_ALGORITHM_SHA256_GUID.as_efi_guid()),
                [3] => guid.write(*HASH_ALGORITHM_SHA384_GUID.as_efi_guid()),
                [4] => guid.write(*HASH_ALGORITHM_SHA512_GUID.as_efi_guid()),
                [] => return efi::Status::INVALID_PARAMETER,
                _ => {}
            }
        }
        efi::Status::SUCCESS
    }

    // The fake cache handle counts lookups and `free_cache` checks it is released once.
    static CACHE_FREES: AtomicUsize = AtomicUsize::new(0);

    extern "efiapi" fn trust_anchor(
        cache: *mut *mut c_void,
        hash: *const u8,
        hash_len: usize,
        _signature: *const u8,
        _signature_len: usize,
        certificate: *mut *mut u8,
        certificate_len: *mut usize,
    ) -> efi::Status {
        // SAFETY: `hash` is readable for `hash_len` bytes and the outputs are writable.
        unsafe {
            let mut lookups = 0u8;
            if !cache.is_null() {
                if (*cache).is_null() {
                    *cache = Box::into_raw(Box::new(0u8)).cast();
                }
                *(*cache).cast::<u8>() += 1;
                lookups = *(*cache).cast::<u8>();
            }
            match input(hash, hash_len) {
                [] => return efi::Status::NOT_FOUND,
                [0] => return efi::Status::SUCCESS,
                hash => {
                    let output = [hash, &[lookups]].concat();
                    certificate.write(pool_buffer(&output));
                    certificate_len.write(output.len());
                }
            }
        }
        efi::Status::SUCCESS
    }
    extern "efiapi" fn free_cache(cache: *mut c_void) {
        // SAFETY: Cache handles come from `trust_anchor`.
        drop(unsafe { Box::from_raw(cache.cast::<u8>()) });
        CACHE_FREES.fetch_add(1, Ordering::SeqCst);
    }
    extern "efiapi" fn timestamp(
        signature: *const u8,
        len: usize,
        _tsa: *const u8,
        _tsa_len: usize,
        time: *mut efi::Time,
    ) -> efi::Boolean {
        if len == 0 {
            return boolean(false);
        }
        // SAFETY: `signature` is readable for `len` bytes and `time` is writable.
        unsafe { (*time).year = u16::from(input(signature, len)[0]) + 2000 };
        boolean(true)
    }

    pub(in crate::one_crypto) fn authenticode() -> OneCryptoProtocolV2 {
        protocol_v2(
            OneCryptoProtocol {
                authenticode_verify: Some(verify),
                image_timestamp_verify: Some(timestamp),
                ..protocol()
            },
            OneCryptoProtocolV2Extension {
                authenticode_verify_ex: Some(verify_ex),
                get_authenticode_hash_algorithm: Some(hash_algorithm),
                get_trust_anchor_x509_from_auth_data: Some(trust_anchor),
                free_trust_anchor_x509_cache: Some(free_cache),
                ..Default::default()
            },
        )
    }

    /// Returns [`authenticode`] as reported by a version 1 provider, which drops the version 2.0 functions.
    fn authenticode_v1() -> OneCryptoProtocol {
        OneCryptoProtocol { major: 1, ..authenticode().base }
    }

    #[test]
    fn test_one_crypto_authenticode_verify() {
        let crypto = crypto_with_frees(authenticode(), 1);
        assert_eq!(crypto.authenticode_verify(&[1], &[], &[1]), Ok(vec![vec![5], vec![6]]));
        assert_eq!(crypto.authenticode_verify(&[1], &[], &[2]), Err(CryptoError::VerificationFailed));
        assert_eq!(crypto.authenticode_verify(&[], &[], &[]), Err(CryptoError::InvalidParameter));
        let without_ex = authenticode();
        let without_ex = OneCryptoProtocolV2 {
            v2: OneCryptoProtocolV2Extension { authenticode_verify_ex: None, ..without_ex.v2 },
            ..without_ex
        };
        for fallback in
            [super::super::test_support::crypto(without_ex), super::super::test_support::crypto(authenticode_v1())]
        {
            assert_eq!(fallback.authenticode_verify(&[1], &[], &[1]), Ok(Vec::new()));
            assert_eq!(fallback.authenticode_verify(&[1], &[], &[2]), Err(CryptoError::VerificationFailed));
        }
    }

    #[test]
    fn test_one_crypto_authenticode_v1_provider() {
        let crypto = crypto(authenticode_v1());
        let crypto: &dyn Signature = &crypto;
        assert_eq!(crypto.authenticode_hash_algorithm(&[1]), Err(CryptoError::Unsupported));
        assert_eq!(crypto.trust_anchor(&[7], &[]), Err(CryptoError::Unsupported));
        assert!(crypto.new_trust_anchor_cache().is_err());
        assert_eq!(crypto.verify_timestamp(&[26], &[]).map(|time| time.year), Ok(2026));
    }

    #[test]
    fn test_one_crypto_authenticode_hash_algorithm() {
        let crypto = crypto(authenticode());
        let crypto: &dyn Signature = &crypto;
        assert_eq!(crypto.authenticode_hash_algorithm(&[1]), Ok(HashAlgorithm::Sha1));
        assert_eq!(crypto.authenticode_hash_algorithm(&[2]), Ok(HashAlgorithm::Sha256));
        assert_eq!(crypto.authenticode_hash_algorithm(&[3]), Ok(HashAlgorithm::Sha384));
        assert_eq!(crypto.authenticode_hash_algorithm(&[4]), Ok(HashAlgorithm::Sha512));
        assert_eq!(crypto.authenticode_hash_algorithm(&[5]), Err(CryptoError::Unsupported));
        assert_eq!(crypto.authenticode_hash_algorithm(&[]), Err(CryptoError::InvalidParameter));
    }

    #[test]
    fn test_one_crypto_authenticode_trust_anchor() {
        let crypto = crypto_with_frees(authenticode(), 3);
        let crypto: &dyn Signature = &crypto;
        assert_eq!(crypto.trust_anchor(&[7], &[]), Ok(vec![7, 0]));
        assert_eq!(crypto.trust_anchor(&[], &[]), Err(CryptoError::NotFound));
        assert_eq!(crypto.trust_anchor(&[0], &[]), Err(CryptoError::NotFound));

        let frees = CACHE_FREES.load(Ordering::SeqCst);
        let mut cache = crypto.new_trust_anchor_cache().expect("cache");
        assert_eq!(cache.trust_anchor(&[7], &[]), Ok(vec![7, 1]));
        assert_eq!(cache.trust_anchor(&[8], &[]), Ok(vec![8, 2]));
        drop(cache);
        assert_eq!(CACHE_FREES.load(Ordering::SeqCst), frees + 1);

        drop(crypto.new_trust_anchor_cache().expect("unused cache"));
        assert_eq!(CACHE_FREES.load(Ordering::SeqCst), frees + 1);
        assert!(super::super::test_support::crypto(protocol()).new_trust_anchor_cache().is_err());
    }

    #[test]
    fn test_one_crypto_authenticode_verify_timestamp() {
        let crypto = crypto(authenticode());
        let crypto: &dyn Signature = &crypto;
        assert_eq!(crypto.verify_timestamp(&[26], &[]).map(|time| time.year), Ok(2026));
        assert_eq!(crypto.verify_timestamp(&[], &[]).map(|time| time.year), Err(CryptoError::VerificationFailed));
    }
}
