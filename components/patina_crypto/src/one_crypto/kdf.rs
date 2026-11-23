//! Key derivation helpers for [`Hash`](crate::service::hash::Hash).
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use super::{OneCrypto, ensure, protocol_fn};
use crate::{
    error::{CryptoError, Result},
    service::hash::{HashAlgorithm, KdfAlgorithm},
};

impl OneCrypto {
    fn pbkdf2(
        &self,
        digest: HashAlgorithm,
        iterations: usize,
        password: &[u8],
        salt: &[u8],
        output: &mut [u8],
    ) -> Result<()> {
        // `Pkcs5HashPassword` only defines SHA-1 and SHA-256.
        if !matches!(digest, HashAlgorithm::Sha1 | HashAlgorithm::Sha256) {
            return Err(CryptoError::Unsupported);
        }
        let hash_password = protocol_fn!(self, pkcs5_hash_password);
        // SAFETY: The inputs are valid for the call and `output` is writable for its length.
        ensure(unsafe {
            hash_password(
                password.len(),
                password.as_ptr(),
                salt.len(),
                salt.as_ptr(),
                iterations,
                digest.digest_size(),
                output.len(),
                output.as_mut_ptr(),
            )
        })
    }

    fn hkdf(&self, digest: HashAlgorithm, key: &[u8], salt: &[u8], info: &[u8], output: &mut [u8]) -> Result<()> {
        let hkdf = match digest {
            HashAlgorithm::Sha256 => protocol_fn!(self, hkdf_sha256_extract_and_expand),
            HashAlgorithm::Sha384 => protocol_fn!(self, hkdf_sha384_extract_and_expand),
            _ => return Err(CryptoError::Unsupported),
        };
        // SAFETY: The inputs are valid for the call and `output` is writable for its length.
        ensure(unsafe {
            hkdf(
                key.as_ptr(),
                key.len(),
                salt.as_ptr(),
                salt.len(),
                info.as_ptr(),
                info.len(),
                output.as_mut_ptr(),
                output.len(),
            )
        })
    }

    fn hkdf_extract(&self, digest: HashAlgorithm, key: &[u8], salt: &[u8], prk: &mut [u8]) -> Result<()> {
        let extract = match digest {
            HashAlgorithm::Sha256 => protocol_fn!(self, hkdf_sha256_extract),
            HashAlgorithm::Sha384 => protocol_fn!(self, hkdf_sha384_extract),
            _ => return Err(CryptoError::Unsupported),
        };
        if prk.len() != digest.digest_size() {
            return Err(CryptoError::InvalidParameter);
        }
        // SAFETY: The inputs are valid for the call and `prk` is writable for its length.
        ensure(unsafe { extract(key.as_ptr(), key.len(), salt.as_ptr(), salt.len(), prk.as_mut_ptr(), prk.len()) })
    }

    fn hkdf_expand(&self, digest: HashAlgorithm, prk: &[u8], info: &[u8], output: &mut [u8]) -> Result<()> {
        let expand = match digest {
            HashAlgorithm::Sha256 => protocol_fn!(self, hkdf_sha256_expand),
            HashAlgorithm::Sha384 => protocol_fn!(self, hkdf_sha384_expand),
            _ => return Err(CryptoError::Unsupported),
        };
        // SAFETY: The inputs are valid for the call and `output` is writable for its length.
        ensure(unsafe { expand(prk.as_ptr(), prk.len(), info.as_ptr(), info.len(), output.as_mut_ptr(), output.len()) })
    }

    /// Derives key material with `algorithm` into `output`.
    pub(super) fn kdf(
        &self,
        algorithm: KdfAlgorithm,
        key: &[u8],
        salt: &[u8],
        info: &[u8],
        output: &mut [u8],
    ) -> Result<()> {
        match algorithm {
            KdfAlgorithm::Pbkdf2 { digest, iterations } if info.is_empty() => {
                self.pbkdf2(digest, iterations, key, salt, output)
            }
            KdfAlgorithm::Hkdf { digest } => self.hkdf(digest, key, salt, info, output),
            KdfAlgorithm::HkdfExtract { digest } if info.is_empty() => self.hkdf_extract(digest, key, salt, output),
            KdfAlgorithm::HkdfExpand { digest } if salt.is_empty() => self.hkdf_expand(digest, key, info, output),
            _ => Err(CryptoError::InvalidParameter),
        }
    }
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
mod tests {
    use patina::standard::efi;

    use crate::service::hash::Hash;

    use super::{
        super::{protocol::OneCryptoProtocol, test_support::*},
        *,
    };

    // Fakes fill the output with the sum of the input sizes.
    #[allow(clippy::too_many_arguments)]
    extern "efiapi" fn hash_password(
        password_len: usize,
        _password: *const u8,
        salt_len: usize,
        _salt: *const u8,
        iterations: usize,
        digest_size: usize,
        out_len: usize,
        out: *mut u8,
    ) -> efi::Boolean {
        // SAFETY: `out` is writable for `out_len` bytes.
        unsafe { out.write_bytes((password_len + salt_len + iterations + digest_size) as u8, out_len) };
        boolean(true)
    }
    #[allow(clippy::too_many_arguments)]
    extern "efiapi" fn extract_and_expand(
        _key: *const u8,
        key_len: usize,
        _salt: *const u8,
        salt_len: usize,
        _info: *const u8,
        info_len: usize,
        out: *mut u8,
        out_len: usize,
    ) -> efi::Boolean {
        // SAFETY: `out` is writable for `out_len` bytes.
        unsafe { out.write_bytes((key_len + salt_len + info_len) as u8, out_len) };
        boolean(true)
    }
    extern "efiapi" fn two_inputs(
        _a: *const u8,
        a_len: usize,
        _b: *const u8,
        b_len: usize,
        out: *mut u8,
        out_len: usize,
    ) -> efi::Boolean {
        // SAFETY: `out` is writable for `out_len` bytes.
        unsafe { out.write_bytes((a_len + b_len) as u8, out_len) };
        boolean(true)
    }

    fn kdf() -> OneCrypto {
        crypto(OneCryptoProtocol {
            pkcs5_hash_password: Some(hash_password),
            hkdf_sha256_extract_and_expand: Some(extract_and_expand),
            hkdf_sha256_extract: Some(two_inputs),
            hkdf_sha256_expand: Some(two_inputs),
            hkdf_sha384_extract: Some(two_inputs),
            ..protocol()
        })
    }

    #[test]
    fn test_one_crypto_kdf_pbkdf2() {
        let mut output = [0u8; 4];
        let pbkdf2 = |digest| KdfAlgorithm::Pbkdf2 { digest, iterations: 3 };
        Hash::derive_key(&kdf(), pbkdf2(HashAlgorithm::Sha256), &[0; 1], &[0; 2], &[], &mut output).expect("pbkdf2");
        assert_eq!(output, [1 + 2 + 3 + 32; 4]);
        assert_eq!(kdf().kdf(pbkdf2(HashAlgorithm::Sha384), &[], &[], &[], &mut output), Err(CryptoError::Unsupported));
        assert_eq!(
            kdf().kdf(pbkdf2(HashAlgorithm::Sha256), &[], &[], &[1], &mut output),
            Err(CryptoError::InvalidParameter)
        );
    }

    #[test]
    fn test_one_crypto_kdf_hkdf() {
        let crypto = kdf();
        let mut output = [0u8; 4];
        let sha256 = HashAlgorithm::Sha256;
        crypto.kdf(KdfAlgorithm::Hkdf { digest: sha256 }, &[0; 1], &[0; 2], &[0; 3], &mut output).expect("hkdf");
        assert_eq!(output, [6; 4]);
        let mut prk = [0u8; 48];
        let extract = KdfAlgorithm::HkdfExtract { digest: HashAlgorithm::Sha384 };
        crypto.kdf(extract, &[0; 1], &[0; 2], &[], &mut prk).expect("extract");
        assert_eq!(prk, [3; 48]);
        assert_eq!(crypto.kdf(extract, &[0; 1], &[0; 2], &[], &mut output), Err(CryptoError::InvalidParameter));
        assert_eq!(crypto.kdf(extract, &[], &[], &[1], &mut prk), Err(CryptoError::InvalidParameter));
        let expand = KdfAlgorithm::HkdfExpand { digest: sha256 };
        crypto.kdf(expand, &[0; 1], &[], &[0; 1], &mut output).expect("expand");
        assert_eq!(output, [2; 4]);
        assert_eq!(crypto.kdf(expand, &[0; 1], &[1], &[0; 1], &mut output), Err(CryptoError::InvalidParameter));
    }

    #[test]
    fn test_one_crypto_kdf_unsupported() {
        let crypto = kdf();
        let mut output = [0u8; 4];
        for digest in [HashAlgorithm::Sha1, HashAlgorithm::Sha384] {
            assert_eq!(
                crypto.kdf(KdfAlgorithm::Hkdf { digest }, &[], &[], &[], &mut output),
                Err(CryptoError::Unsupported)
            );
            assert_eq!(
                crypto.kdf(KdfAlgorithm::HkdfExpand { digest }, &[], &[], &[], &mut output),
                Err(CryptoError::Unsupported)
            );
        }
        assert_eq!(
            crypto.kdf(KdfAlgorithm::HkdfExtract { digest: HashAlgorithm::Sha512 }, &[], &[], &[], &mut output),
            Err(CryptoError::Unsupported)
        );
    }
}
