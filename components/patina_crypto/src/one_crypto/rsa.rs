//! RSA key operations used by the encryption and signature services.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use alloc::vec::Vec;
use core::ffi::c_void;

use super::{
    OneCrypto, ProviderContext, c_string, ensure, ensure_or, optional_c_string_ptr, optional_slice, output_buffer,
    protocol_fn,
};
use crate::{
    error::{CryptoError, Result},
    service::hash::HashAlgorithm,
};

/// The initial output buffer size, large enough for a 4096-bit signature.
const RSA_BUFFER_SIZE: usize = 512;

/// Converts an optional digest into the `DigestLen` parameter of the OAEP functions, where zero selects SHA-1.
fn oaep_digest_len(digest: Option<HashAlgorithm>) -> u16 {
    digest.map_or(0, |digest| digest.digest_size() as u16)
}

/// An RSA key in a provider-allocated context.
pub(super) struct RsaKey {
    crypto: OneCrypto,
    context: ProviderContext,
}

impl RsaKey {
    /// Signs `message_hash` with RSASSA-PKCS1-v1_5.
    pub(super) fn pkcs1_sign(&self, message_hash: &[u8]) -> Result<Vec<u8>> {
        let sign = protocol_fn!(self.crypto, rsa_pkcs1_sign);
        // SAFETY: The context is valid, `message_hash` is valid for the call, and `output_buffer` passes a buffer
        // writable for `*size` bytes.
        output_buffer(RSA_BUFFER_SIZE, |buffer, size| unsafe {
            sign(self.context.as_ptr(), message_hash.as_ptr(), message_hash.len(), buffer, size)
        })
    }

    /// Verifies an RSASSA-PKCS1-v1_5 `signature` over `message_hash`.
    pub(super) fn pkcs1_verify(&self, message_hash: &[u8], signature: &[u8]) -> Result<()> {
        let verify = protocol_fn!(self.crypto, rsa_pkcs1_verify);
        // SAFETY: The context is valid and the inputs are valid for the call.
        let result = unsafe {
            verify(
                self.context.as_ptr(),
                message_hash.as_ptr(),
                message_hash.len(),
                signature.as_ptr(),
                signature.len(),
            )
        };
        ensure_or(result, CryptoError::VerificationFailed)
    }

    /// Signs `message` with RSASSA-PSS.
    pub(super) fn pss_sign(&self, message: &[u8], digest: HashAlgorithm, salt_size: u16) -> Result<Vec<u8>> {
        let sign = protocol_fn!(self.crypto, rsa_pss_sign);
        let digest_len = digest.digest_size() as u16;
        // SAFETY: The context is valid, `message` is valid for the call, and `output_buffer` passes a buffer
        // writable for `*size` bytes.
        output_buffer(RSA_BUFFER_SIZE, |buffer, size| unsafe {
            sign(self.context.as_ptr(), message.as_ptr(), message.len(), digest_len, salt_size, buffer, size)
        })
    }

    /// Verifies an RSASSA-PSS `signature` over `message`.
    pub(super) fn pss_verify(
        &self,
        message: &[u8],
        signature: &[u8],
        digest: HashAlgorithm,
        salt_size: u16,
    ) -> Result<()> {
        let verify = protocol_fn!(self.crypto, rsa_pss_verify);
        // SAFETY: The context is valid and the inputs are valid for the call.
        let result = unsafe {
            verify(
                self.context.as_ptr(),
                message.as_ptr(),
                message.len(),
                signature.as_ptr(),
                signature.len(),
                digest.digest_size() as u16,
                salt_size,
            )
        };
        ensure_or(result, CryptoError::VerificationFailed)
    }

    /// Encrypts `data` with RSAES-OAEP. An empty `prng_seed` is passed as null.
    pub(super) fn oaep_encrypt(&self, data: &[u8], prng_seed: &[u8], digest: Option<HashAlgorithm>) -> Result<Vec<u8>> {
        let encrypt = protocol_fn!(self.crypto, rsa_oaep_encrypt);
        let (seed, seed_size) = optional_slice((!prng_seed.is_empty()).then_some(prng_seed));
        let mut output = core::ptr::null_mut();
        let mut output_size = 0;
        // SAFETY: The context is valid and the inputs are valid for the call. `RsaOaepEncrypt` does not write to
        // the input data despite its non-const signature.
        ensure(unsafe {
            encrypt(
                self.context.as_ptr(),
                data.as_ptr().cast_mut(),
                data.len(),
                seed,
                seed_size,
                oaep_digest_len(digest),
                &mut output,
                &mut output_size,
            )
        })?;
        // SAFETY: On success, `output` is a pool allocation of `output_size` bytes owned by the caller.
        Ok(unsafe { self.crypto.take_pool(output, output_size) })
    }

    /// Decrypts RSAES-OAEP `data`.
    pub(super) fn oaep_decrypt(&self, data: &[u8], digest: Option<HashAlgorithm>) -> Result<Vec<u8>> {
        let decrypt = protocol_fn!(self.crypto, rsa_oaep_decrypt);
        let mut output = core::ptr::null_mut();
        let mut output_size = 0;
        // SAFETY: The context is valid and `data` is valid for the call. `RsaOaepDecrypt` does not write to the
        // input data despite its non-const signature.
        ensure(unsafe {
            decrypt(
                self.context.as_ptr(),
                data.as_ptr().cast_mut(),
                data.len(),
                oaep_digest_len(digest),
                &mut output,
                &mut output_size,
            )
        })?;
        // SAFETY: On success, `output` is a pool allocation of `output_size` bytes owned by the caller.
        Ok(unsafe { self.crypto.take_pool(output, output_size) })
    }
}

impl OneCrypto {
    fn rsa_key(&self, context: *mut c_void) -> Result<RsaKey> {
        // SAFETY: `context` is null or an RSA context allocated by the provider, which `RsaFree` releases.
        let context = unsafe { ProviderContext::new(context, protocol_fn!(self, rsa_free))? };
        Ok(RsaKey { crypto: *self, context })
    }

    /// Loads an RSA private key from PEM, decrypted with `password` if provided.
    pub(super) fn rsa_private_key_from_pem(&self, pem: &[u8], password: Option<&str>) -> Result<RsaKey> {
        let from_pem = protocol_fn!(self, rsa_get_private_key_from_pem);
        protocol_fn!(self, rsa_free);
        let password = password.map(c_string).transpose()?;
        let mut context = core::ptr::null_mut();
        // SAFETY: `pem` is valid for the call and `password` is null or a NUL-terminated string.
        ensure(unsafe { from_pem(pem.as_ptr(), pem.len(), optional_c_string_ptr(&password), &mut context) })?;
        self.rsa_key(context)
    }

    /// Loads the RSA public key from a DER-encoded X.509 certificate.
    pub(super) fn rsa_public_key_from_x509(&self, certificate: &[u8]) -> Result<RsaKey> {
        let from_x509 = protocol_fn!(self, rsa_get_public_key_from_x509);
        protocol_fn!(self, rsa_free);
        let mut context = core::ptr::null_mut();
        // SAFETY: `certificate` is valid for the call.
        ensure(unsafe { from_x509(certificate.as_ptr(), certificate.len(), &mut context) })?;
        self.rsa_key(context)
    }

    /// Decrypts RSAES-OAEP (SHA-1) `data` with a DER-encoded private key.
    pub(super) fn pkcs1v2_decrypt(&self, private_key: &[u8], data: &[u8]) -> Result<Vec<u8>> {
        let decrypt = protocol_fn!(self, pkcs1v2_decrypt);
        let mut output = core::ptr::null_mut();
        let mut output_size = 0;
        // SAFETY: The inputs are valid for the call. `Pkcs1v2Decrypt` does not write to the input data despite its
        // non-const signature.
        ensure(unsafe {
            decrypt(
                private_key.as_ptr(),
                private_key.len(),
                data.as_ptr().cast_mut(),
                data.len(),
                &mut output,
                &mut output_size,
            )
        })?;
        // SAFETY: On success, `output` is a pool allocation of `output_size` bytes owned by the caller.
        Ok(unsafe { self.take_pool(output, output_size) })
    }
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
pub(super) mod tests {
    use alloc::vec;

    use patina::standard::efi;

    use super::{
        super::{protocol::OneCryptoProtocol, test_support::*},
        *,
    };

    // A fake RSA context.
    struct FakeRsa;

    extern "efiapi" fn rsa_new() -> *mut c_void {
        Box::into_raw(Box::new(FakeRsa)).cast()
    }
    extern "efiapi" fn rsa_free(context: *mut c_void) {
        // SAFETY: Contexts come from `rsa_new`.
        drop(unsafe { Box::from_raw(context.cast::<FakeRsa>()) });
    }
    extern "efiapi" fn rsa_pkcs1_sign(
        _context: *mut c_void,
        hash: *const u8,
        hash_len: usize,
        signature: *mut u8,
        size: *mut usize,
    ) -> efi::Boolean {
        // SAFETY: `hash` is readable for `hash_len` bytes and `signature` is writable for `*size` bytes.
        unsafe { write_output(&[input(hash, hash_len), &[0xaa; 600]].concat(), signature, size) }
    }
    extern "efiapi" fn rsa_pkcs1_verify(
        _context: *mut c_void,
        _hash: *const u8,
        hash_len: usize,
        _signature: *const u8,
        signature_len: usize,
    ) -> efi::Boolean {
        boolean(signature_len == hash_len + 600)
    }
    extern "efiapi" fn rsa_pss_sign(
        context: *mut c_void,
        message: *const u8,
        message_len: usize,
        digest_len: u16,
        _salt_len: u16,
        signature: *mut u8,
        size: *mut usize,
    ) -> efi::Boolean {
        assert_eq!(digest_len, 32);
        rsa_pkcs1_sign(context, message, message_len, signature, size)
    }
    extern "efiapi" fn rsa_pss_verify(
        _context: *mut c_void,
        _message: *const u8,
        _message_len: usize,
        _signature: *const u8,
        signature_len: usize,
        _digest_len: u16,
        salt_len: u16,
    ) -> efi::Boolean {
        boolean(signature_len == usize::from(salt_len))
    }
    extern "efiapi" fn rsa_from_x509(_cert: *const u8, len: usize, context: *mut *mut c_void) -> efi::Boolean {
        if len == 0 {
            return boolean(false);
        }
        // SAFETY: `context` is writable.
        unsafe { context.write(rsa_new()) };
        boolean(true)
    }
    extern "efiapi" fn rsa_from_pem(
        _pem: *const u8,
        _len: usize,
        password: *const u8,
        context: *mut *mut c_void,
    ) -> efi::Boolean {
        // SAFETY: `password` is null or a NUL-terminated string.
        if !password.is_null() && unsafe { input(password, 3) } != b"pw\0" {
            return boolean(false);
        }
        rsa_from_x509(core::ptr::null(), 1, context)
    }
    extern "efiapi" fn rsa_oaep_encrypt(
        _context: *mut c_void,
        data: *mut u8,
        data_len: usize,
        _seed: *const u8,
        _seed_len: usize,
        digest_len: u16,
        output: *mut *mut u8,
        output_len: *mut usize,
    ) -> efi::Boolean {
        // SAFETY: `data` is readable for `data_len` bytes and the outputs are writable.
        unsafe {
            output.write(pool_buffer(&[input(data, data_len), &[digest_len as u8]].concat()));
            output_len.write(data_len + 1);
        }
        boolean(true)
    }
    extern "efiapi" fn rsa_oaep_decrypt(
        context: *mut c_void,
        data: *mut u8,
        data_len: usize,
        digest_len: u16,
        output: *mut *mut u8,
        output_len: *mut usize,
    ) -> efi::Boolean {
        rsa_oaep_encrypt(context, data, data_len, core::ptr::null(), 0, digest_len, output, output_len)
    }
    extern "efiapi" fn pkcs1v2_decrypt(
        key: *const u8,
        key_len: usize,
        data: *mut u8,
        data_len: usize,
        output: *mut *mut u8,
        output_len: *mut usize,
    ) -> efi::Boolean {
        let _ = (key, key_len);
        rsa_oaep_encrypt(core::ptr::null_mut(), data, data_len, core::ptr::null(), 0, 0, output, output_len)
    }

    pub(in crate::one_crypto) fn rsa_protocol() -> OneCryptoProtocol {
        OneCryptoProtocol {
            rsa_free: Some(rsa_free),
            rsa_pkcs1_sign: Some(rsa_pkcs1_sign),
            rsa_pkcs1_verify: Some(rsa_pkcs1_verify),
            rsa_pss_sign: Some(rsa_pss_sign),
            rsa_pss_verify: Some(rsa_pss_verify),
            rsa_get_private_key_from_pem: Some(rsa_from_pem),
            rsa_get_public_key_from_x509: Some(rsa_from_x509),
            rsa_oaep_encrypt: Some(rsa_oaep_encrypt),
            rsa_oaep_decrypt: Some(rsa_oaep_decrypt),
            pkcs1v2_decrypt: Some(pkcs1v2_decrypt),
            ..protocol()
        }
    }

    fn key(crypto: &OneCrypto) -> RsaKey {
        crypto.rsa_public_key_from_x509(&[0]).expect("key")
    }

    #[test]
    fn test_one_crypto_rsa_sign_and_verify() {
        let crypto = crypto(rsa_protocol());
        let rsa = key(&crypto);
        let signature = rsa.pkcs1_sign(&[1; 32]).expect("sign");
        assert_eq!(signature.len(), 632);
        assert_eq!(rsa.pkcs1_verify(&[1; 32], &signature), Ok(()));
        assert_eq!(rsa.pkcs1_verify(&[1; 32], &[]), Err(CryptoError::VerificationFailed));
        assert_eq!(rsa.pss_sign(&[1; 4], HashAlgorithm::Sha256, 32).map(|s| s.len()), Ok(604));
        assert_eq!(rsa.pss_verify(&[], &[0; 32], HashAlgorithm::Sha256, 32), Ok(()));
        assert_eq!(rsa.pss_verify(&[], &[], HashAlgorithm::Sha256, 32), Err(CryptoError::VerificationFailed));
    }

    #[test]
    fn test_one_crypto_rsa_oaep_frees_outputs() {
        let crypto = crypto_with_frees(rsa_protocol(), 4);
        let rsa = key(&crypto);
        assert_eq!(rsa.oaep_encrypt(&[1, 2], &[], None), Ok(vec![1, 2, 0]));
        assert_eq!(rsa.oaep_encrypt(&[3], &[9], None), Ok(vec![3, 0]));
        assert_eq!(rsa.oaep_decrypt(&[1], Some(HashAlgorithm::Sha384)), Ok(vec![1, 48]));
        assert_eq!(crypto.pkcs1v2_decrypt(&[0], &[4]), Ok(vec![4, 0]));
    }

    #[test]
    fn test_one_crypto_rsa_key_import() {
        let crypto = crypto(rsa_protocol());
        assert!(crypto.rsa_public_key_from_x509(&[0]).is_ok());
        assert_eq!(crypto.rsa_public_key_from_x509(&[]).err(), Some(CryptoError::Failed));
        assert!(crypto.rsa_private_key_from_pem(&[0], Some("pw")).is_ok());
        assert!(crypto.rsa_private_key_from_pem(&[0], None).is_ok());
        assert_eq!(crypto.rsa_private_key_from_pem(&[0], Some("no")).err(), Some(CryptoError::Failed));
        assert_eq!(crypto.rsa_private_key_from_pem(&[0], Some("p\0w")).err(), Some(CryptoError::InvalidParameter));
    }

    #[test]
    fn test_one_crypto_rsa_requires_free() {
        let crypto = super::super::test_support::crypto(OneCryptoProtocol {
            rsa_get_public_key_from_x509: Some(rsa_from_x509),
            ..protocol()
        });
        assert_eq!(crypto.rsa_public_key_from_x509(&[0]).err(), Some(CryptoError::Unsupported));
    }
}
