//! The PKCS#7 operations used by the signature and encryption services.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use alloc::vec::Vec;

use super::{
    OneCrypto, X509Stack, c_string, ensure, ensure_or, optional_c_string_ptr, parse_cert_stack,
    protocol::{CRYPTO_NID_AES128CBC, CRYPTO_NID_AES192CBC, CRYPTO_NID_AES256CBC, CRYPTO_PKCS7_DEFAULT},
    protocol_fn, protocol_v2_fn, status_to_result,
};
use crate::{
    error::{CryptoError, Result},
    service::{
        encryption::Pkcs7Cipher,
        signature::{Pkcs7CertificateLists, Pkcs7Signers},
    },
};

type FreeSignersFn = unsafe extern "efiapi" fn(*mut u8);

/// Copies a buffer returned by `Pkcs7GetSigners()` or `Pkcs7GetCertificatesList()` and frees it with
/// `Pkcs7FreeSigners()`.
///
/// # Safety
///
/// `data` must be null or a not-yet-freed buffer from the same provider, readable for `len` bytes.
unsafe fn take_signers(free: FreeSignersFn, data: *mut u8, len: usize) -> Vec<u8> {
    if data.is_null() {
        return Vec::new();
    }
    // SAFETY: The caller guarantees `data` is readable for `len` bytes. The bytes are copied before the buffer is
    // freed exactly once.
    unsafe {
        let bytes = core::slice::from_raw_parts(data, len).to_vec();
        free(data);
        bytes
    }
}

fn cipher_nid(cipher: Pkcs7Cipher) -> Result<u32> {
    Ok(match cipher {
        Pkcs7Cipher::Aes128Cbc => CRYPTO_NID_AES128CBC,
        Pkcs7Cipher::Aes192Cbc => CRYPTO_NID_AES192CBC,
        Pkcs7Cipher::Aes256Cbc => CRYPTO_NID_AES256CBC,
        _ => return Err(CryptoError::Unsupported),
    })
}

impl OneCrypto {
    /// Signs `data` and returns DER-encoded PKCS#7 signed data.
    pub(super) fn pkcs7_sign(
        &self,
        private_key: &[u8],
        key_password: Option<&str>,
        data: &[u8],
        signing_certificate: &[u8],
        other_certificates: &[&[u8]],
    ) -> Result<Vec<u8>> {
        let sign = protocol_fn!(self, pkcs7_sign);
        let key_password = key_password.map(c_string).transpose()?;
        let other_certificates = X509Stack::new(self, other_certificates)?;
        let mut signed_data = core::ptr::null_mut();
        let mut signed_data_size = 0;
        // SAFETY: The inputs are valid for the call, `key_password` is null or NUL-terminated, and the stack is
        // null or a provider stack. `Pkcs7Sign` does not write to the input data despite its non-const signature.
        ensure(unsafe {
            sign(
                private_key.as_ptr(),
                private_key.len(),
                optional_c_string_ptr(&key_password),
                data.as_ptr().cast_mut(),
                data.len(),
                signing_certificate.as_ptr(),
                signing_certificate.len(),
                other_certificates.as_ptr(),
                &mut signed_data,
                &mut signed_data_size,
            )
        })?;
        // SAFETY: On success, `signed_data` is a pool allocation of `signed_data_size` bytes owned by the caller.
        Ok(unsafe { self.take_pool(signed_data, signed_data_size) })
    }

    /// Verifies PKCS#7 `signed_data` over `data` against `trusted_certificate`.
    pub(super) fn pkcs7_verify(&self, signed_data: &[u8], trusted_certificate: &[u8], data: &[u8]) -> Result<()> {
        let verify = protocol_fn!(self, pkcs7_verify);
        // SAFETY: The inputs are valid for the call.
        let result = unsafe {
            verify(
                signed_data.as_ptr(),
                signed_data.len(),
                trusted_certificate.as_ptr(),
                trusted_certificate.len(),
                data.as_ptr(),
                data.len(),
            )
        };
        ensure_or(result, CryptoError::VerificationFailed)
    }

    /// Verifies CMS `signed_data` over `data` and returns the signer certificate chain.
    pub(super) fn cms_verify(
        &self,
        signed_data: &[u8],
        trusted_certificate: &[u8],
        data: &[u8],
    ) -> Result<Vec<Vec<u8>>> {
        let cms_verify = protocol_v2_fn!(self, cms_verify);
        let mut chain = core::ptr::null_mut();
        let mut chain_size = 0;
        // SAFETY: The inputs are valid for the call.
        let result = unsafe {
            cms_verify(
                signed_data.as_ptr(),
                signed_data.len(),
                trusted_certificate.as_ptr(),
                trusted_certificate.len(),
                data.as_ptr(),
                data.len(),
                &mut chain,
                &mut chain_size,
            )
        };
        ensure_or(result, CryptoError::VerificationFailed)?;
        // SAFETY: On success, `chain` is a pool allocation of `chain_size` bytes owned by the caller.
        parse_cert_stack(&unsafe { self.take_pool(chain, chain_size) })
    }

    /// Encrypts `data` for `recipients` and returns DER-encoded PKCS#7 enveloped data.
    pub(super) fn pkcs7_encrypt(&self, recipients: &[&[u8]], data: &[u8], cipher: Pkcs7Cipher) -> Result<Vec<u8>> {
        let encrypt = protocol_fn!(self, pkcs7_encrypt);
        let recipients = X509Stack::new(self, recipients)?;
        let mut content_info = core::ptr::null_mut();
        let mut content_info_size = 0;
        // SAFETY: The stack is a provider stack and `data` is valid for the call. `Pkcs7Encrypt` does not write to
        // the input data despite its non-const signature.
        ensure(unsafe {
            encrypt(
                recipients.as_ptr(),
                data.as_ptr().cast_mut(),
                data.len(),
                cipher_nid(cipher)?,
                CRYPTO_PKCS7_DEFAULT,
                &mut content_info,
                &mut content_info_size,
            )
        })?;
        // SAFETY: On success, `content_info` is a pool allocation of `content_info_size` bytes owned by the caller.
        Ok(unsafe { self.take_pool(content_info, content_info_size) })
    }
}

impl OneCrypto {
    pub(super) fn signer_info_count(&self, signed_data: &[u8]) -> usize {
        let Some(count) = self.protocol_v2().and_then(|v2| v2.cms_get_signer_info_num) else {
            return 0;
        };
        // SAFETY: `signed_data` is valid for the call.
        unsafe { count(signed_data.as_ptr(), signed_data.len()) }
    }

    pub(super) fn signers(&self, signed_data: &[u8]) -> Result<Pkcs7Signers> {
        let get_signers = protocol_fn!(self, pkcs7_get_signers);
        let free = protocol_fn!(self, pkcs7_free_signers);
        let (mut stack, mut stack_size) = (core::ptr::null_mut(), 0);
        let (mut trusted, mut trusted_size) = (core::ptr::null_mut(), 0);
        // SAFETY: `signed_data` is valid for the call.
        ensure(unsafe {
            get_signers(
                signed_data.as_ptr(),
                signed_data.len(),
                &mut stack,
                &mut stack_size,
                &mut trusted,
                &mut trusted_size,
            )
        })?;
        // SAFETY: On success, both outputs are buffers of their reported sizes released with `Pkcs7FreeSigners`.
        let (stack, trusted_certificate) =
            unsafe { (take_signers(free, stack, stack_size), take_signers(free, trusted, trusted_size)) };
        Ok(Pkcs7Signers { certificates: parse_cert_stack(&stack)?, trusted_certificate })
    }

    pub(super) fn embedded_certificates(&self, signed_data: &[u8]) -> Result<Pkcs7CertificateLists> {
        let get_certificates = protocol_fn!(self, pkcs7_get_certificates_list);
        let free = protocol_fn!(self, pkcs7_free_signers);
        let (mut chained, mut chained_size) = (core::ptr::null_mut(), 0);
        let (mut unchained, mut unchained_size) = (core::ptr::null_mut(), 0);
        // SAFETY: `signed_data` is valid for the call.
        ensure(unsafe {
            get_certificates(
                signed_data.as_ptr(),
                signed_data.len(),
                &mut chained,
                &mut chained_size,
                &mut unchained,
                &mut unchained_size,
            )
        })?;
        // SAFETY: On success, both outputs are null or buffers of their reported sizes released with
        // `Pkcs7FreeSigners`.
        let (chained, unchained) =
            unsafe { (take_signers(free, chained, chained_size), take_signers(free, unchained, unchained_size)) };
        Ok(Pkcs7CertificateLists {
            signer_chain: parse_cert_stack(&chained)?,
            unchained: parse_cert_stack(&unchained)?,
        })
    }

    pub(super) fn attached_content(&self, signed_data: &[u8]) -> Result<Vec<u8>> {
        let get_content = protocol_fn!(self, pkcs7_get_attached_content);
        let mut content = core::ptr::null_mut();
        let mut content_size = 0;
        // SAFETY: `signed_data` is valid for the call.
        ensure(unsafe { get_content(signed_data.as_ptr(), signed_data.len(), &mut content, &mut content_size) })?;
        if content.is_null() {
            return Err(CryptoError::NotFound);
        }
        // SAFETY: On success, `content` is a pool allocation of `content_size` bytes owned by the caller.
        Ok(unsafe { self.take_pool(content.cast(), content_size) })
    }

    pub(super) fn verify_ekus(&self, signed_data: &[u8], required_ekus: &[&str], require_all: bool) -> Result<()> {
        let verify_ekus = protocol_fn!(self, verify_ekus_in_pkcs7_signature);
        let signature_size = u32::try_from(signed_data.len()).map_err(|_| CryptoError::InvalidParameter)?;
        let eku_count = u32::try_from(required_ekus.len()).map_err(|_| CryptoError::InvalidParameter)?;
        let ekus = required_ekus.iter().map(|eku| c_string(eku)).collect::<Result<Vec<_>>>()?;
        let mut eku_pointers = ekus.iter().map(|eku| eku.as_ptr()).collect::<Vec<_>>();
        // SAFETY: `signed_data` is valid for the call and `eku_pointers` holds `eku_count` NUL-terminated strings.
        status_to_result(unsafe {
            verify_ekus(signed_data.as_ptr(), signature_size, eku_pointers.as_mut_ptr(), eku_count, require_all.into())
        })
    }
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
pub(super) mod tests {
    use alloc::{boxed::Box, vec, vec::Vec};
    use core::ffi::c_void;

    use patina::standard::efi;

    use super::{
        super::{
            protocol::{OneCryptoProtocol, OneCryptoProtocolV2, OneCryptoProtocolV2Extension},
            test_support::*,
        },
        *,
    };
    use crate::service::signature::Signature;

    // Stable Rust cannot define the variadic `X509ConstructCertificateStack`, so tests only use empty stacks.
    extern "efiapi" fn stack_free(_stack: *mut c_void) {
        unreachable!("empty stacks are never freed");
    }
    #[allow(clippy::too_many_arguments)]
    extern "efiapi" fn sign(
        _key: *const u8,
        _key_len: usize,
        password: *const u8,
        data: *mut u8,
        data_len: usize,
        _cert: *const u8,
        _cert_len: usize,
        other_certs: *mut u8,
        signed: *mut *mut u8,
        signed_len: *mut usize,
    ) -> efi::Boolean {
        // SAFETY: `data` is readable for `data_len` bytes and the outputs are writable.
        unsafe {
            let output =
                [input(data, data_len), &[u8::from(other_certs.is_null()), u8::from(!password.is_null())]].concat();
            signed.write(pool_buffer(&output));
            signed_len.write(output.len());
        }
        boolean(true)
    }
    extern "efiapi" fn verify(
        signed: *const u8,
        signed_len: usize,
        _cert: *const u8,
        _cert_len: usize,
        data: *const u8,
        data_len: usize,
    ) -> efi::Boolean {
        // SAFETY: The inputs are readable for their lengths.
        boolean(unsafe { input(signed, signed_len) == input(data, data_len) })
    }
    #[allow(clippy::too_many_arguments)]
    extern "efiapi" fn cms_verify(
        signed: *const u8,
        signed_len: usize,
        cert: *const u8,
        cert_len: usize,
        data: *const u8,
        data_len: usize,
        chain: *mut *mut u8,
        chain_len: *mut usize,
    ) -> efi::Boolean {
        if !bool::from(verify(signed, signed_len, cert, cert_len, data, data_len)) {
            return boolean(false);
        }
        // SAFETY: The outputs are writable.
        unsafe {
            chain.write(pool_buffer(&[1, 1, 0, 0, 0, 9]));
            chain_len.write(6);
        }
        boolean(true)
    }
    extern "efiapi" fn signer_count(_signed: *const u8, len: usize) -> usize {
        len
    }
    // The signer lists are leaked boxed slices that `free_signers` releases.
    fn signer_buffer(data: &[u8]) -> *mut u8 {
        let mut buffer = data.to_vec();
        buffer.resize(16, 0);
        Box::into_raw(buffer.into_boxed_slice()).cast()
    }
    extern "efiapi" fn free_signers(data: *mut u8) {
        // SAFETY: Buffers come from `signer_buffer`.
        drop(unsafe { Box::from_raw(core::ptr::slice_from_raw_parts_mut(data, 16)) });
    }
    extern "efiapi" fn get_signers(
        _signed: *const u8,
        len: usize,
        stack: *mut *mut u8,
        stack_len: *mut usize,
        trusted: *mut *mut u8,
        trusted_len: *mut usize,
    ) -> efi::Boolean {
        if len == 0 {
            return boolean(false);
        }
        // SAFETY: The outputs are writable.
        unsafe {
            stack.write(signer_buffer(&[2, 1, 0, 0, 0, 7, 1, 0, 0, 0, 8]));
            stack_len.write(11);
            trusted.write(signer_buffer(&[8]));
            trusted_len.write(1);
        }
        boolean(true)
    }
    extern "efiapi" fn get_certificates(
        _signed: *const u8,
        _len: usize,
        chained: *mut *mut u8,
        chained_len: *mut usize,
        _unchained: *mut *mut u8,
        _unchained_len: *mut usize,
    ) -> efi::Boolean {
        // SAFETY: The outputs are writable.
        unsafe {
            chained.write(signer_buffer(&[1, 1, 0, 0, 0, 7]));
            chained_len.write(6);
        }
        boolean(true)
    }
    extern "efiapi" fn attached_content(
        signed: *const u8,
        len: usize,
        content: *mut *mut c_void,
        content_len: *mut usize,
    ) -> efi::Boolean {
        if len > 0 {
            // SAFETY: `signed` is readable for `len` bytes and the outputs are writable.
            unsafe {
                content.write(pool_buffer(input(signed, len)).cast());
                content_len.write(len);
            }
        }
        boolean(true)
    }
    extern "efiapi" fn verify_ekus(
        _signed: *const u8,
        _len: u32,
        ekus: *mut *const u8,
        count: u32,
        require_all: efi::Boolean,
    ) -> efi::Status {
        // SAFETY: `ekus` holds `count` NUL-terminated strings.
        let first = unsafe { core::slice::from_raw_parts(ekus, count as usize) }
            .first()
            // SAFETY: Each EKU is NUL-terminated.
            .map(|&eku| unsafe { core::ffi::CStr::from_ptr(eku.cast()) }.to_bytes());
        match (first, bool::from(require_all)) {
            (Some(b"1.2.3"), _) => efi::Status::SUCCESS,
            (_, true) => efi::Status::NOT_FOUND,
            _ => efi::Status::INVALID_PARAMETER,
        }
    }
    extern "efiapi" fn encrypt(
        stack: *mut u8,
        data: *mut u8,
        data_len: usize,
        cipher: u32,
        flags: u32,
        output: *mut *mut u8,
        output_len: *mut usize,
    ) -> efi::Boolean {
        assert_eq!(flags, CRYPTO_PKCS7_DEFAULT);
        // SAFETY: `data` is readable for `data_len` bytes and the outputs are writable.
        unsafe {
            let result = [input(data, data_len), &[u8::from(stack.is_null())], &cipher.to_le_bytes()[..2]].concat();
            output.write(pool_buffer(&result));
            output_len.write(result.len());
        }
        boolean(true)
    }

    pub(in crate::one_crypto) fn pkcs7() -> OneCryptoProtocolV2 {
        protocol_v2(
            OneCryptoProtocol {
                x509_stack_free: Some(stack_free),
                pkcs7_sign: Some(sign),
                pkcs7_verify: Some(verify),
                pkcs7_get_signers: Some(get_signers),
                pkcs7_get_certificates_list: Some(get_certificates),
                pkcs7_free_signers: Some(free_signers),
                pkcs7_get_attached_content: Some(attached_content),
                verify_ekus_in_pkcs7_signature: Some(verify_ekus),
                pkcs7_encrypt: Some(encrypt),
                ..protocol()
            },
            OneCryptoProtocolV2Extension {
                cms_verify: Some(cms_verify),
                cms_get_signer_info_num: Some(signer_count),
                ..Default::default()
            },
        )
    }

    #[test]
    fn test_one_crypto_pkcs7_sign() {
        let crypto = crypto_with_frees(pkcs7(), 2);
        assert_eq!(crypto.pkcs7_sign(&[0], Some("pw"), &[1, 2], &[0], &[]), Ok(vec![1, 2, 1, 1]));
        assert_eq!(crypto.pkcs7_sign(&[0], None, &[1], &[0], &[]), Ok(vec![1, 1, 0]));
        assert_eq!(crypto.pkcs7_sign(&[0], None, &[1], &[0], &[&[3]]), Err(CryptoError::Unsupported));
        assert_eq!(crypto.pkcs7_sign(&[0], Some("p\0w"), &[1], &[0], &[]), Err(CryptoError::InvalidParameter));
    }

    #[test]
    fn test_one_crypto_pkcs7_verify() {
        let crypto = crypto_with_frees(pkcs7(), 1);
        assert_eq!(crypto.pkcs7_verify(&[1], &[], &[1]), Ok(()));
        assert_eq!(crypto.pkcs7_verify(&[1], &[], &[2]), Err(CryptoError::VerificationFailed));
        assert_eq!(crypto.cms_verify(&[1], &[], &[1]), Ok(vec![vec![9]]));
        assert_eq!(crypto.cms_verify(&[1], &[], &[2]), Err(CryptoError::VerificationFailed));
        assert_eq!(Signature::signer_info_count(&crypto, &[0; 3]), 3);
        assert_eq!(super::super::test_support::crypto(protocol()).signer_info_count(&[0; 3]), 0);
        let v1 = super::super::test_support::crypto(OneCryptoProtocol { major: 1, ..pkcs7().base });
        assert_eq!(v1.signer_info_count(&[0; 3]), 0);
        assert_eq!(v1.cms_verify(&[1], &[], &[1]), Err(CryptoError::Unsupported));
    }

    #[test]
    fn test_one_crypto_pkcs7_signers_and_certificates() {
        let crypto = crypto(pkcs7());
        let crypto: &dyn Signature = &crypto;
        assert_eq!(
            crypto.signers(&[0]),
            Ok(Pkcs7Signers { certificates: vec![vec![7], vec![8]], trusted_certificate: vec![8] })
        );
        assert_eq!(crypto.signers(&[]), Err(CryptoError::Failed));
        assert_eq!(
            crypto.embedded_certificates(&[0]),
            Ok(Pkcs7CertificateLists { signer_chain: vec![vec![7]], unchained: Vec::new() })
        );
    }

    #[test]
    fn test_one_crypto_pkcs7_attached_content() {
        let crypto = crypto_with_frees(pkcs7(), 1);
        let crypto: &dyn Signature = &crypto;
        assert_eq!(crypto.attached_content(&[4, 5]), Ok(vec![4, 5]));
        assert_eq!(crypto.attached_content(&[]), Err(CryptoError::NotFound));
    }

    #[test]
    fn test_one_crypto_pkcs7_verify_ekus() {
        let crypto = crypto(pkcs7());
        let crypto: &dyn Signature = &crypto;
        assert_eq!(crypto.verify_ekus(&[0], &["1.2.3", "4.5"], true), Ok(()));
        assert_eq!(crypto.verify_ekus(&[0], &["4.5"], true), Err(CryptoError::NotFound));
        assert_eq!(crypto.verify_ekus(&[0], &[], false), Err(CryptoError::InvalidParameter));
        assert_eq!(crypto.verify_ekus(&[0], &["1\0"], false), Err(CryptoError::InvalidParameter));
    }

    #[test]
    fn test_one_crypto_pkcs7_encrypt() {
        let crypto = crypto_with_frees(pkcs7(), 1);
        let expected = [&[1u8, 1][..], &(CRYPTO_NID_AES256CBC as u16).to_le_bytes()].concat();
        assert_eq!(crypto.pkcs7_encrypt(&[], &[1], Pkcs7Cipher::Aes256Cbc), Ok(expected));
        assert_eq!(crypto.pkcs7_encrypt(&[&[2]], &[1], Pkcs7Cipher::Aes128Cbc), Err(CryptoError::Unsupported));
        assert_eq!(cipher_nid(Pkcs7Cipher::Aes192Cbc), Ok(CRYPTO_NID_AES192CBC));
    }
}
