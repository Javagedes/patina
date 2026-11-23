//! AES operations used by the encryption service.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use alloc::{vec, vec::Vec};
use core::ffi::c_void;

use patina::standard::efi;

use super::{ContextBuffer, OneCrypto, ensure, ensure_or, protocol_fn};
use crate::{
    error::{CryptoError, Result},
    service::encryption::{AES_BLOCK_SIZE, AES_GCM_TAG_SIZE},
};

type CbcFn = unsafe extern "efiapi" fn(*mut c_void, *const u8, usize, *const u8, *mut u8) -> efi::Boolean;

/// An AES key schedule in a caller-allocated context.
pub(super) struct AesCbcKey {
    context: ContextBuffer,
    encrypt: CbcFn,
    decrypt: CbcFn,
}

impl AesCbcKey {
    fn run(&self, operation: CbcFn, input: &[u8], iv: &[u8]) -> Result<Vec<u8>> {
        if input.is_empty() || !input.len().is_multiple_of(AES_BLOCK_SIZE) || iv.len() != AES_BLOCK_SIZE {
            return Err(CryptoError::InvalidParameter);
        }
        let mut output = vec![0u8; input.len()];
        // SAFETY: The context was initialized by `AesInit`, `input` is valid for the call, `iv` holds one block, and
        // `output` has the same size as `input`.
        ensure(unsafe {
            operation(self.context.as_ptr(), input.as_ptr(), input.len(), iv.as_ptr(), output.as_mut_ptr())
        })?;
        Ok(output)
    }

    /// Encrypts `input` in CBC mode.
    pub(super) fn encrypt(&self, input: &[u8], iv: &[u8]) -> Result<Vec<u8>> {
        self.run(self.encrypt, input, iv)
    }

    /// Decrypts `input` in CBC mode.
    pub(super) fn decrypt(&self, input: &[u8], iv: &[u8]) -> Result<Vec<u8>> {
        self.run(self.decrypt, input, iv)
    }
}

impl OneCrypto {
    /// Expands an AES-CBC key schedule for `key`.
    pub(super) fn aes_cbc_key(&self, key: &[u8]) -> Result<AesCbcKey> {
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(CryptoError::InvalidParameter);
        }
        let context_size = protocol_fn!(self, aes_get_context_size);
        let init = protocol_fn!(self, aes_init);
        let encrypt = protocol_fn!(self, aes_cbc_encrypt);
        let decrypt = protocol_fn!(self, aes_cbc_decrypt);
        // SAFETY: `AesGetContextSize` has no preconditions.
        let context = ContextBuffer::new(unsafe { context_size() })?;
        // SAFETY: `context` holds `AesGetContextSize` bytes and `key` is valid for the call. The key length is
        // in bits.
        ensure(unsafe { init(context.as_ptr(), key.as_ptr(), key.len() * 8) })?;
        Ok(AesCbcKey { context, encrypt, decrypt })
    }

    /// Encrypts `plaintext` with AES-GCM and returns the ciphertext followed by the tag.
    pub(super) fn aes_gcm_encrypt(&self, key: &[u8], iv: &[u8], aad: &[u8], plaintext: &[u8]) -> Result<Vec<u8>> {
        let encrypt = protocol_fn!(self, aead_aes_gcm_encrypt);
        let mut output = vec![0u8; plaintext.len() + AES_GCM_TAG_SIZE];
        let (ciphertext, tag) = output.split_at_mut(plaintext.len());
        let mut size = ciphertext.len();
        // SAFETY: The inputs are valid for the call, `tag` holds `AES_GCM_TAG_SIZE` bytes, and `ciphertext` holds
        // `size` bytes.
        let result = unsafe {
            encrypt(
                key.as_ptr(),
                key.len(),
                iv.as_ptr(),
                iv.len(),
                aad.as_ptr(),
                aad.len(),
                plaintext.as_ptr(),
                plaintext.len(),
                tag.as_mut_ptr(),
                tag.len(),
                ciphertext.as_mut_ptr(),
                &mut size,
            )
        };
        ensure_or(result, CryptoError::InvalidParameter)?;
        if size != plaintext.len() {
            return Err(CryptoError::Failed);
        }
        Ok(output)
    }

    /// Decrypts AES-GCM `data`, which is the ciphertext followed by the tag.
    pub(super) fn aes_gcm_decrypt(&self, key: &[u8], iv: &[u8], aad: &[u8], data: &[u8]) -> Result<Vec<u8>> {
        let decrypt = protocol_fn!(self, aead_aes_gcm_decrypt);
        let ciphertext_len = data.len().checked_sub(AES_GCM_TAG_SIZE).ok_or(CryptoError::InvalidParameter)?;
        let (ciphertext, tag) = data.split_at(ciphertext_len);
        let mut plaintext = vec![0u8; ciphertext.len()];
        let mut size = plaintext.len();
        // SAFETY: The inputs are valid for the call and `plaintext` holds `size` bytes.
        let result = unsafe {
            decrypt(
                key.as_ptr(),
                key.len(),
                iv.as_ptr(),
                iv.len(),
                aad.as_ptr(),
                aad.len(),
                ciphertext.as_ptr(),
                ciphertext.len(),
                tag.as_ptr(),
                tag.len(),
                plaintext.as_mut_ptr(),
                &mut size,
            )
        };
        ensure_or(result, CryptoError::VerificationFailed)?;
        plaintext.truncate(size);
        Ok(plaintext)
    }
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
pub(super) mod tests {
    use super::{
        super::{protocol::OneCryptoProtocol, test_support::*},
        *,
    };

    // A fake AES that XORs every byte with the first key byte, stored in the context.
    extern "efiapi" fn context_size() -> usize {
        1
    }
    extern "efiapi" fn init(context: *mut c_void, key: *const u8, bits: usize) -> efi::Boolean {
        assert_eq!(bits % 64, 0);
        // SAFETY: The context holds at least one byte and the key is at least 16 bytes.
        unsafe { context.cast::<u8>().write(*key) };
        boolean(true)
    }
    fn xor_with(key: u8, data: *const u8, len: usize, output: *mut u8) {
        // SAFETY: `data` is readable and `output` writable for `len` bytes.
        unsafe {
            for (i, byte) in input(data, len).iter().enumerate() {
                output.add(i).write(byte ^ key);
            }
        }
    }
    extern "efiapi" fn xor(
        context: *mut c_void,
        data: *const u8,
        len: usize,
        _iv: *const u8,
        output: *mut u8,
    ) -> efi::Boolean {
        // SAFETY: The context holds one byte.
        xor_with(unsafe { *context.cast::<u8>() }, data, len, output);
        boolean(true)
    }

    #[allow(clippy::too_many_arguments)]
    extern "efiapi" fn gcm_encrypt(
        key: *const u8,
        _key_len: usize,
        _iv: *const u8,
        _iv_len: usize,
        _aad: *const u8,
        _aad_len: usize,
        data: *const u8,
        len: usize,
        _tag: *mut u8,
        _tag_len: usize,
        output: *mut u8,
        output_len: *mut usize,
    ) -> efi::Boolean {
        // SAFETY: The key is at least one byte and `output_len` is valid.
        unsafe {
            xor_with(*key, data, len, output);
            *output_len = len;
        }
        boolean(true)
    }

    #[allow(clippy::too_many_arguments)]
    extern "efiapi" fn gcm_decrypt(
        key: *const u8,
        _key_len: usize,
        _iv: *const u8,
        _iv_len: usize,
        _aad: *const u8,
        _aad_len: usize,
        data: *const u8,
        len: usize,
        tag: *const u8,
        _tag_len: usize,
        output: *mut u8,
        output_len: *mut usize,
    ) -> efi::Boolean {
        // SAFETY: The key and tag are at least one byte and `output_len` is valid.
        unsafe {
            if *tag == 0xff {
                return boolean(false);
            }
            xor_with(*key, data, len, output);
            *output_len = len;
        }
        boolean(true)
    }

    pub(in crate::one_crypto) fn aes() -> OneCrypto {
        crypto(OneCryptoProtocol {
            aes_get_context_size: Some(context_size),
            aes_init: Some(init),
            aes_cbc_encrypt: Some(xor),
            aes_cbc_decrypt: Some(xor),
            aead_aes_gcm_encrypt: Some(gcm_encrypt),
            aead_aes_gcm_decrypt: Some(gcm_decrypt),
            ..protocol()
        })
    }

    #[test]
    fn test_one_crypto_aes_cbc_round_trips() {
        let cbc = aes().aes_cbc_key(&[0x5a; 16]).expect("cbc");
        let iv = [0u8; AES_BLOCK_SIZE];
        let ciphertext = cbc.encrypt(&[1; 32], &iv).expect("encrypt");
        assert_eq!(ciphertext, vec![1 ^ 0x5a; 32]);
        assert_eq!(cbc.decrypt(&ciphertext, &iv), Ok(vec![1; 32]));
        assert_eq!(cbc.encrypt(&[1; 15], &iv), Err(CryptoError::InvalidParameter));
        assert_eq!(cbc.encrypt(&[1; 16], &[0; 8]), Err(CryptoError::InvalidParameter));
        assert_eq!(cbc.decrypt(&[], &iv), Err(CryptoError::InvalidParameter));
    }

    #[test]
    fn test_one_crypto_aes_rejects_bad_keys_and_missing_functions() {
        assert_eq!(aes().aes_cbc_key(&[0; 17]).err(), Some(CryptoError::InvalidParameter));
        assert_eq!(crypto(protocol()).aes_cbc_key(&[0; 16]).err(), Some(CryptoError::Unsupported));
        assert_eq!(crypto(protocol()).aes_gcm_decrypt(&[], &[], &[], &[0; 16]), Err(CryptoError::Unsupported));
    }

    #[test]
    fn test_one_crypto_aes_gcm_round_trips() {
        let crypto = aes();
        let encrypted = crypto.aes_gcm_encrypt(&[3; 16], &[0; 12], &[], &[1, 2]).expect("encrypt");
        assert_eq!(encrypted.len(), 2 + AES_GCM_TAG_SIZE);
        assert_eq!(encrypted[..2], [1 ^ 3, 2 ^ 3]);
        assert_eq!(crypto.aes_gcm_decrypt(&[3; 16], &[0; 12], &[], &encrypted), Ok(vec![1, 2]));
        let mut tampered = encrypted.clone();
        tampered[2] = 0xff;
        assert_eq!(crypto.aes_gcm_decrypt(&[3; 16], &[0; 12], &[], &tampered), Err(CryptoError::VerificationFailed));
        assert_eq!(crypto.aes_gcm_decrypt(&[3; 16], &[0; 12], &[], &[0; 15]), Err(CryptoError::InvalidParameter));
    }
}
