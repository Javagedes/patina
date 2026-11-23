//! Elliptic curve key operations used by the signature service.
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
    OneCrypto, ProviderContext, c_string, ensure, ensure_or, optional_c_string_ptr, output_buffer,
    protocol::{CRYPTO_NID_SHA256, CRYPTO_NID_SHA384, CRYPTO_NID_SHA512},
    protocol_fn,
};
use crate::{
    error::{CryptoError, Result},
    service::hash::HashAlgorithm,
};

/// The largest public key or signature size, for P-521 (2 x 66 bytes).
const EC_POINT_SIZE: usize = 132;
fn hash_nid(digest: HashAlgorithm) -> Result<usize> {
    match digest {
        HashAlgorithm::Sha256 => Ok(CRYPTO_NID_SHA256),
        HashAlgorithm::Sha384 => Ok(CRYPTO_NID_SHA384),
        HashAlgorithm::Sha512 => Ok(CRYPTO_NID_SHA512),
        _ => Err(CryptoError::Unsupported),
    }
}

/// An elliptic curve key in a provider-allocated context.
pub(super) struct EcKey {
    crypto: OneCrypto,
    context: ProviderContext,
}

impl EcKey {
    #[cfg(test)]
    pub(super) fn public_key(&self) -> Result<Vec<u8>> {
        let get_public_key = protocol_fn!(self.crypto, ec_get_pub_key);
        // SAFETY: The context is valid and `output_buffer` passes a buffer writable for `*size` bytes.
        output_buffer(EC_POINT_SIZE, |buffer, size| unsafe { get_public_key(self.context.as_ptr(), buffer, size) })
    }

    pub(super) fn dsa_sign(&self, digest: HashAlgorithm, message_hash: &[u8]) -> Result<Vec<u8>> {
        let sign = protocol_fn!(self.crypto, ec_dsa_sign);
        let nid = hash_nid(digest)?;
        // SAFETY: The context is valid, `message_hash` is valid for the call, and `output_buffer` passes a buffer
        // writable for `*size` bytes.
        output_buffer(EC_POINT_SIZE, |buffer, size| unsafe {
            sign(self.context.as_ptr(), nid, message_hash.as_ptr(), message_hash.len(), buffer, size)
        })
    }

    pub(super) fn dsa_verify(&self, digest: HashAlgorithm, message_hash: &[u8], signature: &[u8]) -> Result<()> {
        let verify = protocol_fn!(self.crypto, ec_dsa_verify);
        let nid = hash_nid(digest)?;
        // SAFETY: The context is valid and the inputs are valid for the call.
        let result = unsafe {
            verify(
                self.context.as_ptr(),
                nid,
                message_hash.as_ptr(),
                message_hash.len(),
                signature.as_ptr(),
                signature.len(),
            )
        };
        ensure_or(result, CryptoError::VerificationFailed)
    }
}

impl OneCrypto {
    fn ec_key(&self, context: *mut c_void) -> Result<EcKey> {
        // SAFETY: `context` is null or an EC context allocated by the provider, which `EcFree` releases.
        let context = unsafe { ProviderContext::new(context, protocol_fn!(self, ec_free))? };
        Ok(EcKey { crypto: *self, context })
    }

    /// Loads an EC private key from PEM, decrypted with `password` if provided.
    pub(super) fn ec_private_key_from_pem(&self, pem: &[u8], password: Option<&str>) -> Result<EcKey> {
        let from_pem = protocol_fn!(self, ec_get_private_key_from_pem);
        protocol_fn!(self, ec_free);
        let password = password.map(c_string).transpose()?;
        let mut context = core::ptr::null_mut();
        // SAFETY: `pem` is valid for the call and `password` is null or a NUL-terminated string.
        ensure(unsafe { from_pem(pem.as_ptr(), pem.len(), optional_c_string_ptr(&password), &mut context) })?;
        self.ec_key(context)
    }

    /// Loads the EC public key from a DER-encoded X.509 certificate.
    pub(super) fn ec_public_key_from_x509(&self, certificate: &[u8]) -> Result<EcKey> {
        let from_x509 = protocol_fn!(self, ec_get_public_key_from_x509);
        protocol_fn!(self, ec_free);
        let mut context = core::ptr::null_mut();
        // SAFETY: `certificate` is valid for the call.
        ensure(unsafe { from_x509(certificate.as_ptr(), certificate.len(), &mut context) })?;
        self.ec_key(context)
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

    // A fake EC context that stores a value derived from its source.
    fn new_context(value: usize) -> *mut c_void {
        Box::into_raw(Box::new(value)).cast()
    }
    extern "efiapi" fn ec_free(context: *mut c_void) {
        // SAFETY: Contexts come from `new_context`.
        drop(unsafe { Box::from_raw(context.cast::<usize>()) });
    }
    extern "efiapi" fn ec_key(context: *mut c_void, key: *mut u8, size: *mut usize) -> efi::Boolean {
        // SAFETY: Contexts come from `new_context` and the buffer is writable for `*size` bytes.
        unsafe { write_output(&[*context.cast::<usize>() as u8; 2], key, size) }
    }
    extern "efiapi" fn ec_dsa_sign(
        _context: *mut c_void,
        nid: usize,
        _hash: *const u8,
        _hash_len: usize,
        signature: *mut u8,
        size: *mut usize,
    ) -> efi::Boolean {
        // SAFETY: The buffer is writable for `*size` bytes.
        unsafe { write_output(&[nid as u8], signature, size) }
    }
    extern "efiapi" fn ec_dsa_verify(
        _context: *mut c_void,
        nid: usize,
        _hash: *const u8,
        _hash_len: usize,
        signature: *const u8,
        signature_len: usize,
    ) -> efi::Boolean {
        // SAFETY: `signature` is readable for `signature_len` bytes.
        boolean(unsafe { input(signature, signature_len) } == [nid as u8])
    }
    extern "efiapi" fn ec_from_pem(
        _pem: *const u8,
        _len: usize,
        password: *const u8,
        context: *mut *mut c_void,
    ) -> efi::Boolean {
        // SAFETY: `context` is writable.
        unsafe { context.write(new_context(usize::from(!password.is_null()))) };
        boolean(true)
    }
    extern "efiapi" fn ec_from_x509(_cert: *const u8, len: usize, context: *mut *mut c_void) -> efi::Boolean {
        // SAFETY: `context` is writable.
        unsafe { context.write(new_context(len)) };
        boolean(true)
    }

    fn ec() -> OneCrypto {
        crypto(ec_protocol())
    }

    pub(in crate::one_crypto) fn ec_protocol() -> OneCryptoProtocol {
        OneCryptoProtocol {
            ec_free: Some(ec_free),
            ec_get_pub_key: Some(ec_key),
            ec_dsa_sign: Some(ec_dsa_sign),
            ec_dsa_verify: Some(ec_dsa_verify),
            ec_get_private_key_from_pem: Some(ec_from_pem),
            ec_get_public_key_from_x509: Some(ec_from_x509),
            ..protocol()
        }
    }

    #[test]
    fn test_one_crypto_ec_dsa() {
        let context = ec().ec_private_key_from_pem(&[], None).expect("context");
        let signature = context.dsa_sign(HashAlgorithm::Sha512, &[0; 64]).expect("sign");
        assert_eq!(signature, vec![CRYPTO_NID_SHA512 as u8]);
        assert_eq!(context.dsa_verify(HashAlgorithm::Sha512, &[0; 64], &signature), Ok(()));
        assert_eq!(
            context.dsa_verify(HashAlgorithm::Sha256, &[0; 32], &signature),
            Err(CryptoError::VerificationFailed)
        );
        assert_eq!(context.dsa_sign(HashAlgorithm::Sha1, &[0; 20]), Err(CryptoError::Unsupported));
        assert_eq!(context.dsa_verify(HashAlgorithm::Sha384, &[], &[]), Err(CryptoError::VerificationFailed));
    }

    #[test]
    fn test_one_crypto_ec_key_import() {
        let crypto = ec();
        assert_eq!(crypto.ec_public_key_from_x509(&[0; 3]).expect("x509").public_key(), Ok(vec![3; 2]));
        assert_eq!(crypto.ec_private_key_from_pem(&[], Some("pw")).expect("pem").public_key(), Ok(vec![1; 2]));
        assert_eq!(crypto.ec_private_key_from_pem(&[], None).expect("pem").public_key(), Ok(vec![0; 2]));
        assert_eq!(
            super::super::test_support::crypto(protocol()).ec_public_key_from_x509(&[]).err(),
            Some(CryptoError::Unsupported)
        );
    }
}
