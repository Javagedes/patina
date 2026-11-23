//! `ONE_CRYPTO_PROTOCOL` bindings.
//!
//! The layouts match `CryptoPkg/Include/Protocol/OneCrypto.h` from `mu_basecore`. Version 2.0 of the protocol is the
//! version 1.0 table with additional functions appended, so the bindings are split the same way:
//!
//! - [`OneCryptoProtocol`] is the version 1.0 table, which every compatible provider implements.
//! - [`OneCryptoProtocolV2`] is the version 2.0 table: [`OneCryptoProtocol`] followed by
//!   [`OneCryptoProtocolV2Extension`]. It may only be accessed when the provider reports major version 2 or later.
//!
//! Every function pointer may be `NULL` if the provider does not implement it.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use core::ffi::c_void;

use patina::{BinaryGuid, protocol::ProtocolInterface, standard::efi};

/// The oldest protocol major version these bindings support.
pub const ONE_CRYPTO_VERSION_MAJOR_MIN: u16 = 1;
/// The newest protocol major version these bindings support.
pub const ONE_CRYPTO_VERSION_MAJOR: u16 = 2;

/// `CRYPTO_NID_SHA256`.
pub const CRYPTO_NID_SHA256: usize = 0x0001;
/// `CRYPTO_NID_SHA384`.
pub const CRYPTO_NID_SHA384: usize = 0x0002;
/// `CRYPTO_NID_SHA512`.
pub const CRYPTO_NID_SHA512: usize = 0x0003;
/// `CRYPTO_NID_AES128CBC`.
pub const CRYPTO_NID_AES128CBC: u32 = 0x01A3;
/// `CRYPTO_NID_AES192CBC`.
pub const CRYPTO_NID_AES192CBC: u32 = 0x01A7;
/// `CRYPTO_NID_AES256CBC`.
pub const CRYPTO_NID_AES256CBC: u32 = 0x01AB;
/// `CRYPTO_PKCS7_DEFAULT`.
pub const CRYPTO_PKCS7_DEFAULT: u32 = 0;

/// `gEfiHashAlgorithmSha1Guid`.
pub const HASH_ALGORITHM_SHA1_GUID: BinaryGuid = BinaryGuid::from_string("2ae9d80f-3fb2-4095-b7b1-e93157b946b6");
/// `gEfiHashAlgorithmSha256Guid`.
pub const HASH_ALGORITHM_SHA256_GUID: BinaryGuid = BinaryGuid::from_string("51aa59de-fdf2-4ea3-bc63-875fb7842ee9");
/// `gEfiHashAlgorithmSha384Guid`.
pub const HASH_ALGORITHM_SHA384_GUID: BinaryGuid = BinaryGuid::from_string("efa96432-de33-4dd2-aee6-328c33df777a");
/// `gEfiHashAlgorithmSha512Guid`.
pub const HASH_ALGORITHM_SHA512_GUID: BinaryGuid = BinaryGuid::from_string("caa4381e-750c-4770-b870-7a23b4e42130");

/// `VA_LIST`.
///
/// Only used by `X509ConstructCertificateStackV`, whose ABI depends on the provider's toolchain. Use the
/// variadic `X509ConstructCertificateStack` instead.
pub type VaList = *mut c_void;

/// `BASE_CRYPT_OP_CAPABILITY`.
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct BaseCryptOpCapability {
    /// NUL-terminated algorithm OID string. Points into the same allocation as the capability array.
    pub algorithm_oid: *const u8,
    /// Size of `algorithm_oid` in bytes, including the NUL terminator.
    pub algorithm_oid_size: usize,
}

/// `ONE_CRYPTO_PROTOCOL` version 1.0.
#[repr(C)]
#[derive(Default)]
#[allow(clippy::type_complexity)]
pub struct OneCryptoProtocol {
    /// The protocol major version. A different major version is a breaking change to this structure.
    pub major: u16,
    /// The protocol minor version. Minor versions only add functions to the end of this structure.
    pub minor: u16,
    /// `ONE_CRYPTO_HMAC_SHA256_NEW`.
    pub hmac_sha256_new: Option<unsafe extern "efiapi" fn() -> *mut c_void>,
    /// Frees an HMAC context.
    ///
    /// `ONE_CRYPTO_HMAC_SHA256_FREE`.
    pub hmac_sha256_free: Option<unsafe extern "efiapi" fn(hmac_ctx: *mut c_void)>,
    /// Sets the key for an HMAC context.
    ///
    /// `ONE_CRYPTO_HMAC_SHA256_SET_KEY`.
    pub hmac_sha256_set_key:
        Option<unsafe extern "efiapi" fn(hmac_context: *mut c_void, key: *const u8, key_size: usize) -> efi::Boolean>,
    /// Duplicates an HMAC context.
    ///
    /// `ONE_CRYPTO_HMAC_SHA256_DUPLICATE`.
    pub hmac_sha256_duplicate:
        Option<unsafe extern "efiapi" fn(hmac_context: *const c_void, new_hmac_context: *mut c_void) -> efi::Boolean>,
    /// Updates the HMAC with data.
    ///
    /// `ONE_CRYPTO_HMAC_SHA256_UPDATE`.
    pub hmac_sha256_update: Option<
        unsafe extern "efiapi" fn(hmac_context: *mut c_void, data: *const c_void, data_size: usize) -> efi::Boolean,
    >,
    /// Finalizes the HMAC and produces the HMAC value.
    ///
    /// `ONE_CRYPTO_HMAC_SHA256_FINAL`.
    pub hmac_sha256_final:
        Option<unsafe extern "efiapi" fn(hmac_context: *mut c_void, hmac_value: *mut u8) -> efi::Boolean>,
    /// Performs the entire HMAC operation in one step.
    ///
    /// `ONE_CRYPTO_HMAC_SHA256_ALL`.
    pub hmac_sha256_all: Option<
        unsafe extern "efiapi" fn(
            data: *const c_void,
            data_size: usize,
            key: *const u8,
            key_size: usize,
            hmac_value: *mut u8,
        ) -> efi::Boolean,
    >,
    /// Creates a new HMAC context.
    ///
    /// `ONE_CRYPTO_HMAC_SHA384_NEW`.
    pub hmac_sha384_new: Option<unsafe extern "efiapi" fn() -> *mut c_void>,
    /// Frees an HMAC context.
    ///
    /// `ONE_CRYPTO_HMAC_SHA384_FREE`.
    pub hmac_sha384_free: Option<unsafe extern "efiapi" fn(hmac_ctx: *mut c_void)>,
    /// Sets the key for an HMAC context.
    ///
    /// `ONE_CRYPTO_HMAC_SHA384_SET_KEY`.
    pub hmac_sha384_set_key:
        Option<unsafe extern "efiapi" fn(hmac_context: *mut c_void, key: *const u8, key_size: usize) -> efi::Boolean>,
    /// Duplicates an HMAC context.
    ///
    /// `ONE_CRYPTO_HMAC_SHA384_DUPLICATE`.
    pub hmac_sha384_duplicate:
        Option<unsafe extern "efiapi" fn(hmac_context: *const c_void, new_hmac_context: *mut c_void) -> efi::Boolean>,
    /// Updates the HMAC with data.
    ///
    /// `ONE_CRYPTO_HMAC_SHA384_UPDATE`.
    pub hmac_sha384_update: Option<
        unsafe extern "efiapi" fn(hmac_context: *mut c_void, data: *const c_void, data_size: usize) -> efi::Boolean,
    >,
    /// Finalizes the HMAC and produces the HMAC value.
    ///
    /// `ONE_CRYPTO_HMAC_SHA384_FINAL`.
    pub hmac_sha384_final:
        Option<unsafe extern "efiapi" fn(hmac_context: *mut c_void, hmac_value: *mut u8) -> efi::Boolean>,
    /// Performs the entire HMAC operation in one step.
    ///
    /// `ONE_CRYPTO_HMAC_SHA384_ALL`.
    pub hmac_sha384_all: Option<
        unsafe extern "efiapi" fn(
            data: *const c_void,
            data_size: usize,
            key: *const u8,
            key_size: usize,
            hmac_value: *mut u8,
        ) -> efi::Boolean,
    >,
    /// `ONE_CRYPTO_MD5_GET_CONTEXT_SIZE`.
    pub md5_get_context_size: Option<unsafe extern "efiapi" fn() -> usize>,
    /// Initializes user-supplied memory pointed by Md5Context as MD5 hash context for subsequent use.
    ///
    /// `ONE_CRYPTO_MD5_INIT`.
    pub md5_init: Option<unsafe extern "efiapi" fn(hash_context: *mut c_void) -> efi::Boolean>,
    /// Digests the input data and updates MD5 context.
    ///
    /// `ONE_CRYPTO_MD5_UPDATE`.
    pub md5_update: Option<
        unsafe extern "efiapi" fn(hash_context: *mut c_void, data: *const c_void, data_size: usize) -> efi::Boolean,
    >,
    /// Completes computation of the MD5 digest value.
    ///
    /// `ONE_CRYPTO_MD5_FINAL`.
    pub md5_final: Option<unsafe extern "efiapi" fn(hash_context: *mut c_void, hash_digest: *mut u8) -> efi::Boolean>,
    /// Computes the MD5 message digest of a input data buffer.
    ///
    /// `ONE_CRYPTO_MD5_HASH_ALL`.
    pub md5_hash_all:
        Option<unsafe extern "efiapi" fn(data: *const c_void, data_size: usize, hash_digest: *mut u8) -> efi::Boolean>,
    /// Makes a copy of an existing MD5 context.
    ///
    /// `ONE_CRYPTO_MD5_DUPLICATE`.
    pub md5_duplicate:
        Option<unsafe extern "efiapi" fn(hash_context: *const c_void, new_hash_context: *mut c_void) -> efi::Boolean>,
    /// Retrieves the size, in bytes, of the context buffer required for SHA-1 hash operations.
    ///
    /// `ONE_CRYPTO_SHA1_GET_CONTEXT_SIZE`.
    pub sha1_get_context_size: Option<unsafe extern "efiapi" fn() -> usize>,
    /// Initializes user-supplied memory pointed by Sha1Context as SHA-1 hash context for subsequent use.
    ///
    /// `ONE_CRYPTO_SHA1_INIT`.
    pub sha1_init: Option<unsafe extern "efiapi" fn(hash_context: *mut c_void) -> efi::Boolean>,
    /// Digests the input data and updates SHA-1 context.
    ///
    /// `ONE_CRYPTO_SHA1_UPDATE`.
    pub sha1_update: Option<
        unsafe extern "efiapi" fn(hash_context: *mut c_void, data: *const c_void, data_size: usize) -> efi::Boolean,
    >,
    /// Completes computation of the SHA-1 digest value.
    ///
    /// `ONE_CRYPTO_SHA1_FINAL`.
    pub sha1_final: Option<unsafe extern "efiapi" fn(hash_context: *mut c_void, hash_digest: *mut u8) -> efi::Boolean>,
    /// Computes the SHA-1 message digest of a input data buffer.
    ///
    /// `ONE_CRYPTO_SHA1_HASH_ALL`.
    pub sha1_hash_all:
        Option<unsafe extern "efiapi" fn(data: *const c_void, data_size: usize, hash_digest: *mut u8) -> efi::Boolean>,
    /// Makes a copy of an existing SHA-1 context.
    ///
    /// `ONE_CRYPTO_SHA1_DUPLICATE`.
    pub sha1_duplicate:
        Option<unsafe extern "efiapi" fn(hash_context: *const c_void, new_hash_context: *mut c_void) -> efi::Boolean>,
    /// Retrieves the size, in bytes, of the context buffer required for SHA-256 hash operations.
    ///
    /// `ONE_CRYPTO_SHA256_GET_CONTEXT_SIZE`.
    pub sha256_get_context_size: Option<unsafe extern "efiapi" fn() -> usize>,
    /// Initializes user-supplied memory pointed by Sha256Context as SHA-256 hash context for subsequent use.
    ///
    /// `ONE_CRYPTO_SHA256_INIT`.
    pub sha256_init: Option<unsafe extern "efiapi" fn(hash_context: *mut c_void) -> efi::Boolean>,
    /// Digests the input data and updates SHA-256 context.
    ///
    /// `ONE_CRYPTO_SHA256_UPDATE`.
    pub sha256_update: Option<
        unsafe extern "efiapi" fn(hash_context: *mut c_void, data: *const c_void, data_size: usize) -> efi::Boolean,
    >,
    /// Completes computation of the SHA-256 digest value.
    ///
    /// `ONE_CRYPTO_SHA256_FINAL`.
    pub sha256_final:
        Option<unsafe extern "efiapi" fn(hash_context: *mut c_void, hash_digest: *mut u8) -> efi::Boolean>,
    /// Computes the SHA-256 message digest of a input data buffer.
    ///
    /// `ONE_CRYPTO_SHA256_HASH_ALL`.
    pub sha256_hash_all:
        Option<unsafe extern "efiapi" fn(data: *const c_void, data_size: usize, hash_digest: *mut u8) -> efi::Boolean>,
    /// Makes a copy of an existing SHA-256 context.
    ///
    /// `ONE_CRYPTO_SHA256_DUPLICATE`.
    pub sha256_duplicate:
        Option<unsafe extern "efiapi" fn(hash_context: *const c_void, new_hash_context: *mut c_void) -> efi::Boolean>,
    /// Retrieves the size, in bytes, of the context buffer required for SHA-384 hash operations.
    ///
    /// `ONE_CRYPTO_SHA384_GET_CONTEXT_SIZE`.
    pub sha384_get_context_size: Option<unsafe extern "efiapi" fn() -> usize>,
    /// Initializes user-supplied memory pointed by Sha384Context as SHA-384 hash context for subsequent use.
    ///
    /// `ONE_CRYPTO_SHA384_INIT`.
    pub sha384_init: Option<unsafe extern "efiapi" fn(sha384_context: *mut c_void) -> efi::Boolean>,
    /// Makes a copy of an existing SHA-384 context.
    ///
    /// `ONE_CRYPTO_SHA384_DUPLICATE`.
    pub sha384_duplicate: Option<
        unsafe extern "efiapi" fn(sha384_context: *const c_void, new_sha384_context: *mut c_void) -> efi::Boolean,
    >,
    /// Digests the input data and updates SHA-384 context.
    ///
    /// `ONE_CRYPTO_SHA384_UPDATE`.
    pub sha384_update: Option<
        unsafe extern "efiapi" fn(sha384_context: *mut c_void, data: *const c_void, data_size: usize) -> efi::Boolean,
    >,
    /// Completes computation of the SHA-384 digest value.
    ///
    /// `ONE_CRYPTO_SHA384_FINAL`.
    pub sha384_final:
        Option<unsafe extern "efiapi" fn(sha384_context: *mut c_void, hash_value: *mut u8) -> efi::Boolean>,
    /// Computes the SHA-384 message digest of a input data buffer.
    ///
    /// `ONE_CRYPTO_SHA384_HASH_ALL`.
    pub sha384_hash_all:
        Option<unsafe extern "efiapi" fn(data: *const c_void, data_size: usize, hash_value: *mut u8) -> efi::Boolean>,
    /// Retrieves the size, in bytes, of the context buffer required for SHA-512 hash operations.
    ///
    /// `ONE_CRYPTO_SHA512_GET_CONTEXT_SIZE`.
    pub sha512_get_context_size: Option<unsafe extern "efiapi" fn() -> usize>,
    /// Initializes user-supplied memory pointed by Sha512Context as SHA-512 hash context for subsequent use.
    ///
    /// `ONE_CRYPTO_SHA512_INIT`.
    pub sha512_init: Option<unsafe extern "efiapi" fn(sha512_context: *mut c_void) -> efi::Boolean>,
    /// Makes a copy of an existing SHA-512 context.
    ///
    /// `ONE_CRYPTO_SHA512_DUPLICATE`.
    pub sha512_duplicate: Option<
        unsafe extern "efiapi" fn(sha512_context: *const c_void, new_sha512_context: *mut c_void) -> efi::Boolean,
    >,
    /// Digests the input data and updates SHA-512 context.
    ///
    /// `ONE_CRYPTO_SHA512_UPDATE`.
    pub sha512_update: Option<
        unsafe extern "efiapi" fn(sha512_context: *mut c_void, data: *const c_void, data_size: usize) -> efi::Boolean,
    >,
    /// Completes computation of the SHA-512 digest value.
    ///
    /// `ONE_CRYPTO_SHA512_FINAL`.
    pub sha512_final:
        Option<unsafe extern "efiapi" fn(sha512_context: *mut c_void, hash_value: *mut u8) -> efi::Boolean>,
    /// Computes the SHA-512 message digest of a input data buffer.
    ///
    /// `ONE_CRYPTO_SHA512_HASH_ALL`.
    pub sha512_hash_all:
        Option<unsafe extern "efiapi" fn(data: *const c_void, data_size: usize, hash_value: *mut u8) -> efi::Boolean>,
    /// Retrieves the size, in bytes, of the context buffer required for SM3 hash operations.
    ///
    /// `ONE_CRYPTO_SM3_GET_CONTEXT_SIZE`.
    pub sm3_get_context_size: Option<unsafe extern "efiapi" fn() -> usize>,
    /// Initializes user-supplied memory pointed by Sm3Context as SM3 hash context for subsequent use.
    ///
    /// `ONE_CRYPTO_SM3_INIT`.
    pub sm3_init: Option<unsafe extern "efiapi" fn(sm3_context: *mut c_void) -> efi::Boolean>,
    /// Makes a copy of an existing SM3 context.
    ///
    /// `ONE_CRYPTO_SM3_DUPLICATE`.
    pub sm3_duplicate:
        Option<unsafe extern "efiapi" fn(sm3_context: *const c_void, new_sm3_context: *mut c_void) -> efi::Boolean>,
    /// Digests the input data and updates SM3 context.
    ///
    /// `ONE_CRYPTO_SM3_UPDATE`.
    pub sm3_update: Option<
        unsafe extern "efiapi" fn(sm3_context: *mut c_void, data: *const c_void, data_size: usize) -> efi::Boolean,
    >,
    /// Completes computation of the SM3 digest value.
    ///
    /// `ONE_CRYPTO_SM3_FINAL`.
    pub sm3_final: Option<unsafe extern "efiapi" fn(sm3_context: *mut c_void, hash_value: *mut u8) -> efi::Boolean>,
    /// Computes the SM3 message digest of a input data buffer.
    ///
    /// `ONE_CRYPTO_SM3_HASH_ALL`.
    pub sm3_hash_all:
        Option<unsafe extern "efiapi" fn(data: *const c_void, data_size: usize, hash_value: *mut u8) -> efi::Boolean>,
    /// `ONE_CRYPTO_AES_GET_CONTEXT_SIZE`.
    pub aes_get_context_size: Option<unsafe extern "efiapi" fn() -> usize>,
    /// Initializes user-supplied memory as AES context for subsequent use.
    ///
    /// `ONE_CRYPTO_AES_INIT`.
    pub aes_init:
        Option<unsafe extern "efiapi" fn(aes_context: *mut c_void, key: *const u8, key_length: usize) -> efi::Boolean>,
    /// Performs AES encryption on a data buffer of the specified size in CBC mode.
    ///
    /// `ONE_CRYPTO_AES_CBC_ENCRYPT`.
    pub aes_cbc_encrypt: Option<
        unsafe extern "efiapi" fn(
            aes_context: *mut c_void,
            input: *const u8,
            input_size: usize,
            ivec: *const u8,
            output: *mut u8,
        ) -> efi::Boolean,
    >,
    /// Performs AES decryption on a data buffer of the specified size in CBC mode.
    ///
    /// `ONE_CRYPTO_AES_CBC_DECRYPT`.
    pub aes_cbc_decrypt: Option<
        unsafe extern "efiapi" fn(
            aes_context: *mut c_void,
            input: *const u8,
            input_size: usize,
            ivec: *const u8,
            output: *mut u8,
        ) -> efi::Boolean,
    >,
    /// Performs AEAD AES-GCM authenticated encryption on a data buffer and additional authenticated data (AAD).
    ///
    /// `ONE_CRYPTO_AEAD_AES_GCM_ENCRYPT`.
    pub aead_aes_gcm_encrypt: Option<
        unsafe extern "efiapi" fn(
            key: *const u8,
            key_size: usize,
            iv: *const u8,
            iv_size: usize,
            a_data: *const u8,
            a_data_size: usize,
            data_in: *const u8,
            data_in_size: usize,
            tag_out: *mut u8,
            tag_size: usize,
            data_out: *mut u8,
            data_out_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Performs AEAD AES-GCM authenticated decryption on a data buffer and additional authenticated data (AAD).
    ///
    /// `ONE_CRYPTO_AEAD_AES_GCM_DECRYPT`.
    pub aead_aes_gcm_decrypt: Option<
        unsafe extern "efiapi" fn(
            key: *const u8,
            key_size: usize,
            iv: *const u8,
            iv_size: usize,
            a_data: *const u8,
            a_data_size: usize,
            data_in: *const u8,
            data_in_size: usize,
            tag: *const u8,
            tag_size: usize,
            data_out: *mut u8,
            data_out_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// `ONE_CRYPTO_BIG_NUM_INIT`.
    pub big_num_init: Option<unsafe extern "efiapi" fn() -> *mut c_void>,
    /// Allocate new Big Number and assign the provided value to it.
    ///
    /// `ONE_CRYPTO_BIG_NUM_FROM_BIN`.
    pub big_num_from_bin: Option<unsafe extern "efiapi" fn(buf: *const u8, len: usize) -> *mut c_void>,
    /// Convert the absolute value of Bn into big-endian form and store it at Buf.
    ///
    /// `ONE_CRYPTO_BIG_NUM_TO_BIN`.
    pub big_num_to_bin: Option<unsafe extern "efiapi" fn(bn: *const c_void, buf: *mut u8) -> isize>,
    /// Free the Big Number.
    ///
    /// `ONE_CRYPTO_BIG_NUM_FREE`.
    pub big_num_free: Option<unsafe extern "efiapi" fn(bn: *mut c_void, clear: efi::Boolean)>,
    /// Calculate the sum of two Big Numbers.
    ///
    /// `ONE_CRYPTO_BIG_NUM_ADD`.
    pub big_num_add: Option<
        unsafe extern "efiapi" fn(bn_a: *const c_void, bn_b: *const c_void, bn_res: *mut c_void) -> efi::Boolean,
    >,
    /// Subtract two Big Numbers.
    ///
    /// `ONE_CRYPTO_BIG_NUM_SUB`.
    pub big_num_sub: Option<
        unsafe extern "efiapi" fn(bn_a: *const c_void, bn_b: *const c_void, bn_res: *mut c_void) -> efi::Boolean,
    >,
    /// Calculate remainder: BnRes = BnA % BnB.
    ///
    /// `ONE_CRYPTO_BIG_NUM_MOD`.
    pub big_num_mod: Option<
        unsafe extern "efiapi" fn(bn_a: *const c_void, bn_b: *const c_void, bn_res: *mut c_void) -> efi::Boolean,
    >,
    /// Compute BnA to the BnP-th power modulo BnM.
    ///
    /// `ONE_CRYPTO_BIG_NUM_EXP_MOD`.
    pub big_num_exp_mod: Option<
        unsafe extern "efiapi" fn(
            bn_a: *const c_void,
            bn_p: *const c_void,
            bn_m: *const c_void,
            bn_res: *mut c_void,
        ) -> efi::Boolean,
    >,
    /// Compute BnA inverse modulo BnM.
    ///
    /// `ONE_CRYPTO_BIG_NUM_INVERSE_MOD`.
    pub big_num_inverse_mod: Option<
        unsafe extern "efiapi" fn(bn_a: *const c_void, bn_m: *const c_void, bn_res: *mut c_void) -> efi::Boolean,
    >,
    /// Divide two Big Numbers.
    ///
    /// `ONE_CRYPTO_BIG_NUM_DIV`.
    pub big_num_div: Option<
        unsafe extern "efiapi" fn(bn_a: *const c_void, bn_b: *const c_void, bn_res: *mut c_void) -> efi::Boolean,
    >,
    /// Multiply two Big Numbers modulo BnM.
    ///
    /// `ONE_CRYPTO_BIG_NUM_MUL_MOD`.
    pub big_num_mul_mod: Option<
        unsafe extern "efiapi" fn(
            bn_a: *const c_void,
            bn_b: *const c_void,
            bn_m: *const c_void,
            bn_res: *mut c_void,
        ) -> efi::Boolean,
    >,
    /// Compare two Big Numbers.
    ///
    /// `ONE_CRYPTO_BIG_NUM_CMP`.
    pub big_num_cmp: Option<unsafe extern "efiapi" fn(bn_a: *const c_void, bn_b: *const c_void) -> isize>,
    /// Get number of bits in Bn.
    ///
    /// `ONE_CRYPTO_BIG_NUM_BITS`.
    pub big_num_bits: Option<unsafe extern "efiapi" fn(bn: *const c_void) -> usize>,
    /// Get number of bytes in Bn.
    ///
    /// `ONE_CRYPTO_BIG_NUM_BYTES`.
    pub big_num_bytes: Option<unsafe extern "efiapi" fn(bn: *const c_void) -> usize>,
    /// Checks if Big Number equals to the given Num.
    ///
    /// `ONE_CRYPTO_BIG_NUM_IS_WORD`.
    pub big_num_is_word: Option<unsafe extern "efiapi" fn(bn: *const c_void, num: usize) -> efi::Boolean>,
    /// Checks if Big Number is odd.
    ///
    /// `ONE_CRYPTO_BIG_NUM_IS_ODD`.
    pub big_num_is_odd: Option<unsafe extern "efiapi" fn(bn: *const c_void) -> efi::Boolean>,
    /// Copy Big number.
    ///
    /// `ONE_CRYPTO_BIG_NUM_COPY`.
    pub big_num_copy: Option<unsafe extern "efiapi" fn(bn_dst: *mut c_void, bn_src: *const c_void) -> *mut c_void>,
    /// Get constant Big number with value of "1".
    ///
    /// `ONE_CRYPTO_BIG_NUM_VALUE_ONE`.
    pub big_num_value_one: Option<unsafe extern "efiapi" fn() -> *const c_void>,
    /// Shift right Big Number.
    ///
    /// `ONE_CRYPTO_BIG_NUM_R_SHIFT`.
    pub big_num_r_shift:
        Option<unsafe extern "efiapi" fn(bn: *const c_void, n: usize, bn_res: *mut c_void) -> efi::Boolean>,
    /// Mark Big Number for constant time computations.
    ///
    /// `ONE_CRYPTO_BIG_NUM_CONST_TIME`.
    pub big_num_const_time: Option<unsafe extern "efiapi" fn(bn: *mut c_void)>,
    /// Calculate square modulo.
    ///
    /// `ONE_CRYPTO_BIG_NUM_SQR_MOD`.
    pub big_num_sqr_mod: Option<
        unsafe extern "efiapi" fn(bn_a: *const c_void, bn_m: *const c_void, bn_res: *mut c_void) -> efi::Boolean,
    >,
    /// Create new Big Number computation context.
    ///
    /// `ONE_CRYPTO_BIG_NUM_NEW_CONTEXT`.
    pub big_num_new_context: Option<unsafe extern "efiapi" fn() -> *mut c_void>,
    /// Free Big Number context that was allocated with BigNumNewContext().
    ///
    /// `ONE_CRYPTO_BIG_NUM_CONTEXT_FREE`.
    pub big_num_context_free: Option<unsafe extern "efiapi" fn(bn_ctx: *mut c_void)>,
    /// Set Big Number to a given value.
    ///
    /// `ONE_CRYPTO_BIG_NUM_SET_UINT`.
    pub big_num_set_uint: Option<unsafe extern "efiapi" fn(bn: *mut c_void, val: usize) -> efi::Boolean>,
    /// Add two Big Numbers modulo BnM.
    ///
    /// `ONE_CRYPTO_BIG_NUM_ADD_MOD`.
    pub big_num_add_mod: Option<
        unsafe extern "efiapi" fn(
            bn_a: *const c_void,
            bn_b: *const c_void,
            bn_m: *const c_void,
            bn_res: *mut c_void,
        ) -> efi::Boolean,
    >,
    /// `ONE_CRYPTO_HKDF_SHA256_EXTRACT_AND_EXPAND`.
    pub hkdf_sha256_extract_and_expand: Option<
        unsafe extern "efiapi" fn(
            key: *const u8,
            key_size: usize,
            salt: *const u8,
            salt_size: usize,
            info: *const u8,
            info_size: usize,
            out: *mut u8,
            out_size: usize,
        ) -> efi::Boolean,
    >,
    /// Derive HMAC-SHA*-based Extract key Derivation Function (HKDF).
    ///
    /// `ONE_CRYPTO_HKDF_SHA256_EXTRACT`.
    pub hkdf_sha256_extract: Option<
        unsafe extern "efiapi" fn(
            key: *const u8,
            key_size: usize,
            salt: *const u8,
            salt_size: usize,
            prk_out: *mut u8,
            prk_out_size: usize,
        ) -> efi::Boolean,
    >,
    /// Derive HMAC-SHA*-based Expand Key Derivation Function (HKDF).
    ///
    /// `ONE_CRYPTO_HKDF_SHA256_EXPAND`.
    pub hkdf_sha256_expand: Option<
        unsafe extern "efiapi" fn(
            prk: *const u8,
            prk_size: usize,
            info: *const u8,
            info_size: usize,
            out: *mut u8,
            out_size: usize,
        ) -> efi::Boolean,
    >,
    /// Derive key data using HMAC-SHA* based KDF.
    ///
    /// `ONE_CRYPTO_HKDF_SHA384_EXTRACT_AND_EXPAND`.
    pub hkdf_sha384_extract_and_expand: Option<
        unsafe extern "efiapi" fn(
            key: *const u8,
            key_size: usize,
            salt: *const u8,
            salt_size: usize,
            info: *const u8,
            info_size: usize,
            out: *mut u8,
            out_size: usize,
        ) -> efi::Boolean,
    >,
    /// Derive HMAC-SHA*-based Extract key Derivation Function (HKDF).
    ///
    /// `ONE_CRYPTO_HKDF_SHA384_EXTRACT`.
    pub hkdf_sha384_extract: Option<
        unsafe extern "efiapi" fn(
            key: *const u8,
            key_size: usize,
            salt: *const u8,
            salt_size: usize,
            prk_out: *mut u8,
            prk_out_size: usize,
        ) -> efi::Boolean,
    >,
    /// Derive HMAC-SHA*-based Expand Key Derivation Function (HKDF).
    ///
    /// `ONE_CRYPTO_HKDF_SHA384_EXPAND`.
    pub hkdf_sha384_expand: Option<
        unsafe extern "efiapi" fn(
            prk: *const u8,
            prk_size: usize,
            info: *const u8,
            info_size: usize,
            out: *mut u8,
            out_size: usize,
        ) -> efi::Boolean,
    >,
    /// `ONE_CRYPTO_AUTHENTICODE_VERIFY`.
    pub authenticode_verify: Option<
        unsafe extern "efiapi" fn(
            auth_data: *const u8,
            data_size: usize,
            trusted_cert: *const u8,
            cert_size: usize,
            image_hash: *const u8,
            hash_size: usize,
        ) -> efi::Boolean,
    >,
    /// Encrypts a blob using PKCS1v2 (RSAES-OAEP) schema.
    ///
    /// `ONE_CRYPTO_PKCS1V2_ENCRYPT`.
    pub pkcs1v2_encrypt: Option<
        unsafe extern "efiapi" fn(
            public_key: *const u8,
            public_key_size: usize,
            in_data: *mut u8,
            in_data_size: usize,
            prng_seed: *const u8,
            prng_seed_size: usize,
            encrypted_data: *mut *mut u8,
            encrypted_data_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Decrypts a blob using PKCS1v2 (RSAES-OAEP) schema.
    ///
    /// `ONE_CRYPTO_PKCS1V2_DECRYPT`.
    pub pkcs1v2_decrypt: Option<
        unsafe extern "efiapi" fn(
            private_key: *const u8,
            private_key_size: usize,
            encrypted_data: *mut u8,
            encrypted_data_size: usize,
            out_data: *mut *mut u8,
            out_data_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Encrypts a blob using PKCS1v2 (RSAES-OAEP) schema.
    ///
    /// `ONE_CRYPTO_RSA_OAEP_ENCRYPT`.
    pub rsa_oaep_encrypt: Option<
        unsafe extern "efiapi" fn(
            rsa_context: *mut c_void,
            in_data: *mut u8,
            in_data_size: usize,
            prng_seed: *const u8,
            prng_seed_size: usize,
            digest_len: u16,
            encrypted_data: *mut *mut u8,
            encrypted_data_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Decrypts a blob using PKCS1v2 (RSAES-OAEP) schema.
    ///
    /// `ONE_CRYPTO_RSA_OAEP_DECRYPT`.
    pub rsa_oaep_decrypt: Option<
        unsafe extern "efiapi" fn(
            rsa_context: *mut c_void,
            encrypted_data: *mut u8,
            encrypted_data_size: usize,
            digest_len: u16,
            out_data: *mut *mut u8,
            out_data_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Derives a key from a password using a salt and iteration count, based on PKCS#5 v2.0 password based encryption key derivation function PBKDF2, as specified in RFC 2898.
    ///
    /// `ONE_CRYPTO_PKCS5_HASH_PASSWORD`.
    pub pkcs5_hash_password: Option<
        unsafe extern "efiapi" fn(
            password_length: usize,
            password: *const u8,
            salt_length: usize,
            salt: *const u8,
            iteration_count: usize,
            digest_size: usize,
            key_length: usize,
            out_key: *mut u8,
        ) -> efi::Boolean,
    >,
    /// Get the signer's certificates from PKCS#7 signed data as described in "PKCS #7: Cryptographic Message Syntax Standard".
    ///
    /// `ONE_CRYPTO_PKCS7_GET_SIGNERS`.
    pub pkcs7_get_signers: Option<
        unsafe extern "efiapi" fn(
            p7_data: *const u8,
            p7_length: usize,
            cert_stack: *mut *mut u8,
            stack_length: *mut usize,
            trusted_cert: *mut *mut u8,
            cert_length: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Wrap function to use free() to free allocated memory for certificates.
    ///
    /// `ONE_CRYPTO_PKCS7_FREE_SIGNERS`.
    pub pkcs7_free_signers: Option<unsafe extern "efiapi" fn(certs: *mut u8)>,
    /// Retrieves all embedded certificates from PKCS#7 signed data as described in "PKCS #7: Cryptographic Message Syntax Standard", and outputs two certificate lists chained and unchained to the signer's certificates.
    ///
    /// `ONE_CRYPTO_PKCS7_GET_CERTIFICATES_LIST`.
    pub pkcs7_get_certificates_list: Option<
        unsafe extern "efiapi" fn(
            p7_data: *const u8,
            p7_length: usize,
            signer_chain_certs: *mut *mut u8,
            chain_length: *mut usize,
            unchain_certs: *mut *mut u8,
            unchain_length: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Creates a PKCS#7 signedData as described in "PKCS #7: Cryptographic Message Syntax Standard, version 1.5".
    ///
    /// `ONE_CRYPTO_PKCS7_SIGN`.
    pub pkcs7_sign: Option<
        unsafe extern "efiapi" fn(
            private_key: *const u8,
            private_key_size: usize,
            key_password: *const u8,
            in_data: *mut u8,
            in_data_size: usize,
            sign_cert: *const u8,
            sign_cert_size: usize,
            other_certs: *mut u8,
            signed_data: *mut *mut u8,
            signed_data_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Verifies the validity of a PKCS#7 signed data as described in "PKCS #7: Cryptographic Message Syntax Standard".
    ///
    /// `ONE_CRYPTO_PKCS7_VERIFY`.
    pub pkcs7_verify: Option<
        unsafe extern "efiapi" fn(
            p7_data: *const u8,
            p7_length: usize,
            trusted_cert: *const u8,
            cert_length: usize,
            in_data: *const u8,
            data_length: usize,
        ) -> efi::Boolean,
    >,
    /// Creates a DER-encoded PKCS#7 ContentInfo containing an envelopedData structure that wraps content encrypted for secure transmission to one or more recipients.
    ///
    /// `ONE_CRYPTO_PKCS7_ENCRYPT`.
    pub pkcs7_encrypt: Option<
        unsafe extern "efiapi" fn(
            x509_stack: *mut u8,
            in_data: *mut u8,
            in_data_size: usize,
            cipher_nid: u32,
            flags: u32,
            content_info: *mut *mut u8,
            content_info_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// This function receives a PKCS7 formatted signature, and then verifies that the specified Enhanced or Extended Key Usages (EKU's) are present in the end-entity leaf signing certificate.
    ///
    /// `ONE_CRYPTO_VERIFY_EK_US_IN_PKCS7_SIGNATURE`.
    pub verify_ekus_in_pkcs7_signature: Option<
        unsafe extern "efiapi" fn(
            pkcs7_signature: *const u8,
            signature_size: u32,
            required_ekus: *mut *const u8,
            required_ekus_size: u32,
            require_all_present: efi::Boolean,
        ) -> efi::Status,
    >,
    /// Extracts the attached content from a PKCS#7 signed data if existed.
    ///
    /// `ONE_CRYPTO_PKCS7_GET_ATTACHED_CONTENT`.
    pub pkcs7_get_attached_content: Option<
        unsafe extern "efiapi" fn(
            p7_data: *const u8,
            p7_length: usize,
            content: *mut *mut c_void,
            content_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// `ONE_CRYPTO_DH_NEW`.
    pub dh_new: Option<unsafe extern "efiapi" fn() -> *mut c_void>,
    /// Release the specified DH context.
    ///
    /// `ONE_CRYPTO_DH_FREE`.
    pub dh_free: Option<unsafe extern "efiapi" fn(dh_context: *mut c_void)>,
    /// Generates DH parameter.
    ///
    /// `ONE_CRYPTO_DH_GENERATE_PARAMETER`.
    pub dh_generate_parameter: Option<
        unsafe extern "efiapi" fn(
            dh_context: *mut c_void,
            generator: usize,
            prime_length: usize,
            prime: *mut u8,
        ) -> efi::Boolean,
    >,
    /// Sets generator and prime parameters for DH.
    ///
    /// `ONE_CRYPTO_DH_SET_PARAMETER`.
    pub dh_set_parameter: Option<
        unsafe extern "efiapi" fn(
            dh_context: *mut c_void,
            generator: usize,
            prime_length: usize,
            prime: *const u8,
        ) -> efi::Boolean,
    >,
    /// Generates DH public key.
    ///
    /// `ONE_CRYPTO_DH_GENERATE_KEY`.
    pub dh_generate_key: Option<
        unsafe extern "efiapi" fn(
            dh_context: *mut c_void,
            public_key: *mut u8,
            public_key_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Computes exchanged common key.
    ///
    /// `ONE_CRYPTO_DH_COMPUTE_KEY`.
    pub dh_compute_key: Option<
        unsafe extern "efiapi" fn(
            dh_context: *mut c_void,
            peer_public_key: *const u8,
            peer_public_key_size: usize,
            key: *mut u8,
            key_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// `ONE_CRYPTO_EC_GROUP_INIT`.
    pub ec_group_init: Option<unsafe extern "efiapi" fn(crypto_nid: usize) -> *mut c_void>,
    /// Get EC curve parameters.
    ///
    /// `ONE_CRYPTO_EC_GROUP_GET_CURVE`.
    pub ec_group_get_curve: Option<
        unsafe extern "efiapi" fn(
            ec_group: *const c_void,
            bn_prime: *mut c_void,
            bn_a: *mut c_void,
            bn_b: *mut c_void,
            bn_ctx: *mut c_void,
        ) -> efi::Boolean,
    >,
    /// Get EC group order.
    ///
    /// `ONE_CRYPTO_EC_GROUP_GET_ORDER`.
    pub ec_group_get_order:
        Option<unsafe extern "efiapi" fn(ec_group: *mut c_void, bn_order: *mut c_void) -> efi::Boolean>,
    /// Free previously allocated EC group object using EcGroupInit().
    ///
    /// `ONE_CRYPTO_EC_GROUP_FREE`.
    pub ec_group_free: Option<unsafe extern "efiapi" fn(ec_group: *mut c_void)>,
    /// Initialize new opaque EC Point object.
    ///
    /// `ONE_CRYPTO_EC_POINT_INIT`.
    pub ec_point_init: Option<unsafe extern "efiapi" fn(ec_group: *const c_void) -> *mut c_void>,
    /// Free previously allocated EC Point object using EcPointInit().
    ///
    /// `ONE_CRYPTO_EC_POINT_DE_INIT`.
    pub ec_point_de_init: Option<unsafe extern "efiapi" fn(ec_point: *mut c_void, clear: efi::Boolean)>,
    /// Get EC point affine (x,y) coordinates.
    ///
    /// `ONE_CRYPTO_EC_POINT_GET_AFFINE_COORDINATES`.
    pub ec_point_get_affine_coordinates: Option<
        unsafe extern "efiapi" fn(
            ec_group: *const c_void,
            ec_point: *const c_void,
            bn_x: *mut c_void,
            bn_y: *mut c_void,
            bn_ctx: *mut c_void,
        ) -> efi::Boolean,
    >,
    /// Set EC point affine (x,y) coordinates.
    ///
    /// `ONE_CRYPTO_EC_POINT_SET_AFFINE_COORDINATES`.
    pub ec_point_set_affine_coordinates: Option<
        unsafe extern "efiapi" fn(
            ec_group: *const c_void,
            ec_point: *mut c_void,
            bn_x: *const c_void,
            bn_y: *const c_void,
            bn_ctx: *mut c_void,
        ) -> efi::Boolean,
    >,
    /// EC Point addition.
    ///
    /// `ONE_CRYPTO_EC_POINT_ADD`.
    pub ec_point_add: Option<
        unsafe extern "efiapi" fn(
            ec_group: *const c_void,
            ec_point_result: *mut c_void,
            ec_point_a: *const c_void,
            ec_point_b: *const c_void,
            bn_ctx: *mut c_void,
        ) -> efi::Boolean,
    >,
    /// Variable EC point multiplication.
    ///
    /// `ONE_CRYPTO_EC_POINT_MUL`.
    pub ec_point_mul: Option<
        unsafe extern "efiapi" fn(
            ec_group: *const c_void,
            ec_point_result: *mut c_void,
            ec_point: *const c_void,
            bn_p_scalar: *const c_void,
            bn_ctx: *mut c_void,
        ) -> efi::Boolean,
    >,
    /// Calculate the inverse of the supplied EC point.
    ///
    /// `ONE_CRYPTO_EC_POINT_INVERT`.
    pub ec_point_invert: Option<
        unsafe extern "efiapi" fn(ec_group: *const c_void, ec_point: *mut c_void, bn_ctx: *mut c_void) -> efi::Boolean,
    >,
    /// Check if the supplied point is on EC curve.
    ///
    /// `ONE_CRYPTO_EC_POINT_IS_ON_CURVE`.
    pub ec_point_is_on_curve: Option<
        unsafe extern "efiapi" fn(
            ec_group: *const c_void,
            ec_point: *const c_void,
            bn_ctx: *mut c_void,
        ) -> efi::Boolean,
    >,
    /// Check if the supplied point is at infinity.
    ///
    /// `ONE_CRYPTO_EC_POINT_IS_AT_INFINITY`.
    pub ec_point_is_at_infinity:
        Option<unsafe extern "efiapi" fn(ec_group: *const c_void, ec_point: *const c_void) -> efi::Boolean>,
    /// Check if EC points are equal.
    ///
    /// `ONE_CRYPTO_EC_POINT_EQUAL`.
    pub ec_point_equal: Option<
        unsafe extern "efiapi" fn(
            ec_group: *const c_void,
            ec_point_a: *const c_void,
            ec_point_b: *const c_void,
            bn_ctx: *mut c_void,
        ) -> efi::Boolean,
    >,
    /// Set EC point compressed coordinates.
    ///
    /// `ONE_CRYPTO_EC_POINT_SET_COMPRESSED_COORDINATES`.
    pub ec_point_set_compressed_coordinates: Option<
        unsafe extern "efiapi" fn(
            ec_group: *const c_void,
            ec_point: *mut c_void,
            bn_x: *const c_void,
            y_bit: u8,
            bn_ctx: *mut c_void,
        ) -> efi::Boolean,
    >,
    /// Allocates and Initializes one Elliptic Curve Context for subsequent use with the NID.
    ///
    /// `ONE_CRYPTO_EC_NEW_BY_NID`.
    pub ec_new_by_nid: Option<unsafe extern "efiapi" fn(nid: usize) -> *mut c_void>,
    /// Release the specified EC context.
    ///
    /// `ONE_CRYPTO_EC_FREE`.
    pub ec_free: Option<unsafe extern "efiapi" fn(ec_context: *mut c_void)>,
    /// Generates EC key and returns EC public key (X, Y), Please note, this function uses pseudo random number generator.
    ///
    /// `ONE_CRYPTO_EC_GENERATE_KEY`.
    pub ec_generate_key: Option<
        unsafe extern "efiapi" fn(
            ec_context: *mut c_void,
            public_key: *mut u8,
            public_key_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Gets the public key component from the established EC context.
    ///
    /// `ONE_CRYPTO_EC_GET_PUB_KEY`.
    pub ec_get_pub_key: Option<
        unsafe extern "efiapi" fn(
            ec_context: *mut c_void,
            public_key: *mut u8,
            public_key_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Computes exchanged common key.
    ///
    /// `ONE_CRYPTO_EC_DH_COMPUTE_KEY`.
    pub ec_dh_compute_key: Option<
        unsafe extern "efiapi" fn(
            ec_context: *mut c_void,
            peer_public: *const u8,
            peer_public_size: usize,
            compress_flag: *const i32,
            key: *mut u8,
            key_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Retrieve the EC Private Key from the password-protected PEM key data.
    ///
    /// `ONE_CRYPTO_EC_GET_PRIVATE_KEY_FROM_PEM`.
    pub ec_get_private_key_from_pem: Option<
        unsafe extern "efiapi" fn(
            pem_data: *const u8,
            pem_size: usize,
            password: *const u8,
            ec_context: *mut *mut c_void,
        ) -> efi::Boolean,
    >,
    /// Retrieve the EC Public Key from one DER-encoded X509 certificate.
    ///
    /// `ONE_CRYPTO_EC_GET_PUBLIC_KEY_FROM_X509`.
    pub ec_get_public_key_from_x509: Option<
        unsafe extern "efiapi" fn(cert: *const u8, cert_size: usize, ec_context: *mut *mut c_void) -> efi::Boolean,
    >,
    /// Carries out the EC-DSA signature.
    ///
    /// `ONE_CRYPTO_EC_DSA_SIGN`.
    pub ec_dsa_sign: Option<
        unsafe extern "efiapi" fn(
            ec_context: *mut c_void,
            hash_nid: usize,
            message_hash: *const u8,
            hash_size: usize,
            signature: *mut u8,
            sig_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Verifies the EC-DSA signature.
    ///
    /// `ONE_CRYPTO_EC_DSA_VERIFY`.
    pub ec_dsa_verify: Option<
        unsafe extern "efiapi" fn(
            ec_context: *mut c_void,
            hash_nid: usize,
            message_hash: *const u8,
            hash_size: usize,
            signature: *const u8,
            sig_size: usize,
        ) -> efi::Boolean,
    >,
    /// `ONE_CRYPTO_RSA_NEW`.
    pub rsa_new: Option<unsafe extern "efiapi" fn() -> *mut c_void>,
    /// Release the specified RSA context.
    ///
    /// `ONE_CRYPTO_RSA_FREE`.
    pub rsa_free: Option<unsafe extern "efiapi" fn(rsa_context: *mut c_void)>,
    /// Sets the tag-designated key component into the established RSA context.
    ///
    /// `ONE_CRYPTO_RSA_SET_KEY`.
    pub rsa_set_key: Option<
        unsafe extern "efiapi" fn(
            rsa_context: *mut c_void,
            key_tag: u32,
            big_number: *const u8,
            bn_size: usize,
        ) -> efi::Boolean,
    >,
    /// Gets the tag-designated RSA key component from the established RSA context.
    ///
    /// `ONE_CRYPTO_RSA_GET_KEY`.
    pub rsa_get_key: Option<
        unsafe extern "efiapi" fn(
            rsa_context: *mut c_void,
            key_tag: u32,
            big_number: *mut u8,
            bn_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Generates RSA key components.
    ///
    /// `ONE_CRYPTO_RSA_GENERATE_KEY`.
    pub rsa_generate_key: Option<
        unsafe extern "efiapi" fn(
            rsa_context: *mut c_void,
            modulus_length: usize,
            public_exponent: *const u8,
            public_exponent_size: usize,
        ) -> efi::Boolean,
    >,
    /// Validates key components of RSA context.
    ///
    /// `ONE_CRYPTO_RSA_CHECK_KEY`.
    pub rsa_check_key: Option<unsafe extern "efiapi" fn(rsa_context: *mut c_void) -> efi::Boolean>,
    /// Carries out the RSA-SSA signature generation with EMSA-PKCS1-v1_5 encoding scheme.
    ///
    /// `ONE_CRYPTO_RSA_PKCS1_SIGN`.
    pub rsa_pkcs1_sign: Option<
        unsafe extern "efiapi" fn(
            rsa_context: *mut c_void,
            message_hash: *const u8,
            hash_size: usize,
            signature: *mut u8,
            sig_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Verifies the RSA-SSA signature with EMSA-PKCS1-v1_5 encoding scheme defined in RSA PKCS#1.
    ///
    /// `ONE_CRYPTO_RSA_PKCS1_VERIFY`.
    pub rsa_pkcs1_verify: Option<
        unsafe extern "efiapi" fn(
            rsa_context: *mut c_void,
            message_hash: *const u8,
            hash_size: usize,
            signature: *const u8,
            sig_size: usize,
        ) -> efi::Boolean,
    >,
    /// Carries out the RSA-SSA signature generation with EMSA-PSS encoding scheme.
    ///
    /// `ONE_CRYPTO_RSA_PSS_SIGN`.
    pub rsa_pss_sign: Option<
        unsafe extern "efiapi" fn(
            rsa_context: *mut c_void,
            message: *const u8,
            msg_size: usize,
            digest_len: u16,
            salt_len: u16,
            signature: *mut u8,
            sig_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Verifies the RSA signature with RSASSA-PSS signature scheme defined in RFC 8017.
    ///
    /// `ONE_CRYPTO_RSA_PSS_VERIFY`.
    pub rsa_pss_verify: Option<
        unsafe extern "efiapi" fn(
            rsa_context: *mut c_void,
            message: *const u8,
            msg_size: usize,
            signature: *const u8,
            sig_size: usize,
            digest_len: u16,
            salt_len: u16,
        ) -> efi::Boolean,
    >,
    /// Retrieve the RSA Private Key from the password-protected PEM key data.
    ///
    /// `ONE_CRYPTO_RSA_GET_PRIVATE_KEY_FROM_PEM`.
    pub rsa_get_private_key_from_pem: Option<
        unsafe extern "efiapi" fn(
            pem_data: *const u8,
            pem_size: usize,
            password: *const u8,
            rsa_context: *mut *mut c_void,
        ) -> efi::Boolean,
    >,
    /// Retrieve the RSA Public Key from one DER-encoded X509 certificate.
    ///
    /// `ONE_CRYPTO_RSA_GET_PUBLIC_KEY_FROM_X509`.
    pub rsa_get_public_key_from_x509: Option<
        unsafe extern "efiapi" fn(cert: *const u8, cert_size: usize, rsa_context: *mut *mut c_void) -> efi::Boolean,
    >,
    /// `ONE_CRYPTO_X509_GET_SUBJECT_NAME`.
    pub x509_get_subject_name: Option<
        unsafe extern "efiapi" fn(
            cert: *const u8,
            cert_size: usize,
            cert_subject: *mut u8,
            subject_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Retrieve the common name (CN) string from one X.509 certificate.
    ///
    /// `ONE_CRYPTO_X509_GET_COMMON_NAME`.
    pub x509_get_common_name: Option<
        unsafe extern "efiapi" fn(
            cert: *const u8,
            cert_size: usize,
            common_name: *mut u8,
            common_name_size: *mut usize,
        ) -> efi::Status,
    >,
    /// Retrieve the organization name (O) string from one X.509 certificate.
    ///
    /// `ONE_CRYPTO_X509_GET_ORGANIZATION_NAME`.
    pub x509_get_organization_name: Option<
        unsafe extern "efiapi" fn(
            cert: *const u8,
            cert_size: usize,
            name_buffer: *mut u8,
            name_buffer_size: *mut usize,
        ) -> efi::Status,
    >,
    /// Verify one X509 certificate was issued by the trusted CA.
    ///
    /// `ONE_CRYPTO_X509_VERIFY_CERT`.
    pub x509_verify_cert: Option<
        unsafe extern "efiapi" fn(
            cert: *const u8,
            cert_size: usize,
            ca_cert: *const u8,
            ca_cert_size: usize,
        ) -> efi::Boolean,
    >,
    /// Construct a X509 object from DER-encoded certificate data.
    ///
    /// `ONE_CRYPTO_X509_CONSTRUCT_CERTIFICATE`.
    pub x509_construct_certificate: Option<
        unsafe extern "efiapi" fn(cert: *const u8, cert_size: usize, single_x509_cert: *mut *mut u8) -> efi::Boolean,
    >,
    /// Construct a X509 stack object from a list of DER-encoded certificate data.
    ///
    /// `ONE_CRYPTO_X509_CONSTRUCT_CERTIFICATE_STACK_V`.
    pub x509_construct_certificate_stack_v:
        Option<unsafe extern "efiapi" fn(x509_stack: *mut *mut u8, args: VaList) -> efi::Boolean>,
    /// Construct a X509 stack object from a list of DER-encoded certificate data.
    ///
    /// `ONE_CRYPTO_X509_CONSTRUCT_CERTIFICATE_STACK`.
    pub x509_construct_certificate_stack:
        Option<unsafe extern "efiapi" fn(x509_stack: *mut *mut u8, ...) -> efi::Boolean>,
    /// Release the specified X509 object.
    ///
    /// `ONE_CRYPTO_X509_FREE`.
    pub x509_free: Option<unsafe extern "efiapi" fn(x509_cert: *mut c_void)>,
    /// Release the specified X509 stack object.
    ///
    /// `ONE_CRYPTO_X509_STACK_FREE`.
    pub x509_stack_free: Option<unsafe extern "efiapi" fn(x509_stack: *mut c_void)>,
    /// Retrieve the TBSCertificate from one given X.509 certificate.
    ///
    /// `ONE_CRYPTO_X509_GET_TBS_CERT`.
    pub x509_get_tbs_cert: Option<
        unsafe extern "efiapi" fn(
            cert: *const u8,
            cert_size: usize,
            tbs_cert: *mut *mut u8,
            tbs_cert_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Retrieve the version from one X.509 certificate.
    ///
    /// `ONE_CRYPTO_X509_GET_VERSION`.
    pub x509_get_version:
        Option<unsafe extern "efiapi" fn(cert: *const u8, cert_size: usize, version: *mut usize) -> efi::Boolean>,
    /// Retrieve the serialNumber from one X.509 certificate.
    ///
    /// `ONE_CRYPTO_X509_GET_SERIAL_NUMBER`.
    pub x509_get_serial_number: Option<
        unsafe extern "efiapi" fn(
            cert: *const u8,
            cert_size: usize,
            serial_number: *mut u8,
            serial_number_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Retrieve the issuer bytes from one X.509 certificate.
    ///
    /// `ONE_CRYPTO_X509_GET_ISSUER_NAME`.
    pub x509_get_issuer_name: Option<
        unsafe extern "efiapi" fn(
            cert: *const u8,
            cert_size: usize,
            cert_issuer: *mut u8,
            cert_issuer_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Retrieve the Signature Algorithm from one X.509 certificate.
    ///
    /// `ONE_CRYPTO_X509_GET_SIGNATURE_ALGORITHM`.
    pub x509_get_signature_algorithm: Option<
        unsafe extern "efiapi" fn(
            cert: *const u8,
            cert_size: usize,
            oid: *mut u8,
            oid_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Retrieve the Extended Key Usage from one X.509 certificate.
    ///
    /// `ONE_CRYPTO_X509_GET_EXTENDED_KEY_USAGE`.
    pub x509_get_extended_key_usage: Option<
        unsafe extern "efiapi" fn(
            cert: *const u8,
            cert_size: usize,
            usage: *mut u8,
            usage_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Retrieve Extension data from one X.509 certificate.
    ///
    /// `ONE_CRYPTO_X509_GET_EXTENSION_DATA`.
    pub x509_get_extension_data: Option<
        unsafe extern "efiapi" fn(
            cert: *const u8,
            cert_size: usize,
            oid: *const u8,
            oid_size: usize,
            extension_data: *mut u8,
            extension_data_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Retrieve the Validity from one X.509 certificate
    ///
    /// `ONE_CRYPTO_X509_GET_VALIDITY`.
    pub x509_get_validity: Option<
        unsafe extern "efiapi" fn(
            cert: *const u8,
            cert_size: usize,
            from: *mut u8,
            from_size: *mut usize,
            to: *mut u8,
            to_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Format a DateTimeStr to DataTime object in DataTime Buffer
    ///
    /// `ONE_CRYPTO_X509_FORMAT_DATE_TIME`.
    pub x509_format_date_time: Option<
        unsafe extern "efiapi" fn(
            date_time_str: *const u8,
            date_time: *mut c_void,
            date_time_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Retrieve the Key Usage from one X.509 certificate.
    ///
    /// `ONE_CRYPTO_X509_GET_KEY_USAGE`.
    pub x509_get_key_usage:
        Option<unsafe extern "efiapi" fn(cert: *const u8, cert_size: usize, usage: *mut usize) -> efi::Boolean>,
    /// Verify one X509 certificate was issued by the trusted CA.
    ///
    /// `ONE_CRYPTO_X509_VERIFY_CERT_CHAIN`.
    pub x509_verify_cert_chain: Option<
        unsafe extern "efiapi" fn(
            root_cert: *const u8,
            root_cert_length: usize,
            cert_chain: *const u8,
            cert_chain_length: usize,
        ) -> efi::Boolean,
    >,
    /// Get one X509 certificate from CertChain.
    ///
    /// `ONE_CRYPTO_X509_GET_CERT_FROM_CERT_CHAIN`.
    pub x509_get_cert_from_cert_chain: Option<
        unsafe extern "efiapi" fn(
            cert_chain: *const u8,
            cert_chain_length: usize,
            cert_index: i32,
            cert: *mut *const u8,
            cert_length: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Retrieve the basic constraints from one X.509 certificate.
    ///
    /// `ONE_CRYPTO_X509_GET_EXTENDED_BASIC_CONSTRAINTS`.
    pub x509_get_extended_basic_constraints: Option<
        unsafe extern "efiapi" fn(
            cert: *const u8,
            cert_size: usize,
            basic_constraints: *mut u8,
            basic_constraints_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Retrieve the tag and length of the tag.
    ///
    /// `ONE_CRYPTO_ASN1_GET_TAG`.
    pub asn1_get_tag: Option<
        unsafe extern "efiapi" fn(ptr: *mut *mut u8, end_: *const u8, length: *mut usize, tag: u32) -> efi::Boolean,
    >,
    /// Compare DateTime1 object and DateTime2 object.
    ///
    /// `ONE_CRYPTO_X509_COMPARE_DATE_TIME`.
    pub x509_compare_date_time:
        Option<unsafe extern "efiapi" fn(date_time1: *const c_void, date_time2: *const c_void) -> i32>,
    /// `ONE_CRYPTO_RANDOM_SEED`.
    pub random_seed: Option<unsafe extern "efiapi" fn(seed: *const u8, seed_size: usize) -> efi::Boolean>,
    /// Generates a pseudorandom byte stream of the specified size.
    ///
    /// `ONE_CRYPTO_RANDOM_BYTES`.
    pub random_bytes: Option<unsafe extern "efiapi" fn(output: *mut u8, size: usize) -> efi::Boolean>,
    /// `ONE_CRYPTO_TLS_INITIALIZE`.
    pub tls_initialize: Option<unsafe extern "efiapi" fn() -> efi::Boolean>,
    /// Free an allocated SSL_CTX object.
    ///
    /// `ONE_CRYPTO_TLS_CTX_FREE`.
    pub tls_ctx_free: Option<unsafe extern "efiapi" fn(tls_ctx: *mut c_void)>,
    /// Creates a new SSL_CTX object as framework to establish TLS/SSL enabled connections.
    ///
    /// `ONE_CRYPTO_TLS_CTX_NEW`.
    pub tls_ctx_new: Option<unsafe extern "efiapi" fn(major_ver: u8, minor_ver: u8) -> *mut c_void>,
    /// Free an allocated TLS object.
    ///
    /// `ONE_CRYPTO_TLS_FREE`.
    pub tls_free: Option<unsafe extern "efiapi" fn(tls: *mut c_void)>,
    /// Create a new TLS object for a connection.
    ///
    /// `ONE_CRYPTO_TLS_NEW`.
    pub tls_new: Option<unsafe extern "efiapi" fn(tls_ctx: *mut c_void) -> *mut c_void>,
    /// Checks if the TLS handshake was done.
    ///
    /// `ONE_CRYPTO_TLS_IN_HANDSHAKE`.
    pub tls_in_handshake: Option<unsafe extern "efiapi" fn(tls: *mut c_void) -> efi::Boolean>,
    /// Perform a TLS/SSL handshake.
    ///
    /// `ONE_CRYPTO_TLS_DO_HANDSHAKE`.
    pub tls_do_handshake: Option<
        unsafe extern "efiapi" fn(
            tls: *mut c_void,
            buffer_in: *mut u8,
            buffer_in_size: usize,
            buffer_out: *mut u8,
            buffer_out_size: *mut usize,
        ) -> efi::Status,
    >,
    /// Handle Alert message recorded in BufferIn.
    ///
    /// `ONE_CRYPTO_TLS_HANDLE_ALERT`.
    pub tls_handle_alert: Option<
        unsafe extern "efiapi" fn(
            tls: *mut c_void,
            buffer_in: *mut u8,
            buffer_in_size: usize,
            buffer_out: *mut u8,
            buffer_out_size: *mut usize,
        ) -> efi::Status,
    >,
    /// Build the CloseNotify packet.
    ///
    /// `ONE_CRYPTO_TLS_CLOSE_NOTIFY`.
    pub tls_close_notify:
        Option<unsafe extern "efiapi" fn(tls: *mut c_void, buffer: *mut u8, buffer_size: *mut usize) -> efi::Status>,
    /// Attempts to read bytes from one TLS object and places the data in Buffer.
    ///
    /// `ONE_CRYPTO_TLS_CTRL_TRAFFIC_OUT`.
    pub tls_ctrl_traffic_out:
        Option<unsafe extern "efiapi" fn(tls: *mut c_void, buffer: *mut c_void, buffer_size: usize) -> isize>,
    /// Attempts to write data from the buffer to TLS object.
    ///
    /// `ONE_CRYPTO_TLS_CTRL_TRAFFIC_IN`.
    pub tls_ctrl_traffic_in:
        Option<unsafe extern "efiapi" fn(tls: *mut c_void, buffer: *mut c_void, buffer_size: usize) -> isize>,
    /// Attempts to read bytes from the specified TLS connection into the buffer.
    ///
    /// `ONE_CRYPTO_TLS_READ`.
    pub tls_read: Option<unsafe extern "efiapi" fn(tls: *mut c_void, buffer: *mut c_void, buffer_size: usize) -> isize>,
    /// Attempts to write data to a TLS connection.
    ///
    /// `ONE_CRYPTO_TLS_WRITE`.
    pub tls_write:
        Option<unsafe extern "efiapi" fn(tls: *mut c_void, buffer: *mut c_void, buffer_size: usize) -> isize>,
    /// Shutdown a TLS connection.
    ///
    /// `ONE_CRYPTO_TLS_SHUTDOWN`.
    pub tls_shutdown: Option<unsafe extern "efiapi" fn(tls: *mut c_void) -> efi::Status>,
    /// Set a new TLS/SSL method for a particular TLS object.
    ///
    /// `ONE_CRYPTO_TLS_SET_VERSION`.
    pub tls_set_version:
        Option<unsafe extern "efiapi" fn(tls: *mut c_void, major_ver: u8, minor_ver: u8) -> efi::Status>,
    /// Set TLS object to work in client or server mode.
    ///
    /// `ONE_CRYPTO_TLS_SET_CONNECTION_END`.
    pub tls_set_connection_end:
        Option<unsafe extern "efiapi" fn(tls: *mut c_void, is_server: efi::Boolean) -> efi::Status>,
    /// Set the ciphers list to be used by the TLS object.
    ///
    /// `ONE_CRYPTO_TLS_SET_CIPHER_LIST`.
    pub tls_set_cipher_list:
        Option<unsafe extern "efiapi" fn(tls: *mut c_void, cipher_id: *mut u16, cipher_num: usize) -> efi::Status>,
    /// Set the compression method for TLS/SSL operations.
    ///
    /// `ONE_CRYPTO_TLS_SET_COMPRESSION_METHOD`.
    pub tls_set_compression_method: Option<unsafe extern "efiapi" fn(comp_method: u8) -> efi::Status>,
    /// Set peer certificate verification mode for the TLS connection.
    ///
    /// `ONE_CRYPTO_TLS_SET_VERIFY`.
    pub tls_set_verify: Option<unsafe extern "efiapi" fn(tls: *mut c_void, verify_mode: u32)>,
    /// Set the specified host name to be verified.
    ///
    /// `ONE_CRYPTO_TLS_SET_VERIFY_HOST`.
    pub tls_set_verify_host:
        Option<unsafe extern "efiapi" fn(tls: *mut c_void, flags: u32, host_name: *mut u8) -> efi::Status>,
    /// Sets a TLS/SSL session ID to be used during TLS/SSL connect.
    ///
    /// `ONE_CRYPTO_TLS_SET_SESSION_ID`.
    pub tls_set_session_id:
        Option<unsafe extern "efiapi" fn(tls: *mut c_void, session_id: *mut u8, session_id_len: u16) -> efi::Status>,
    /// Adds the CA to the cert store when requesting Server or Client authentication.
    ///
    /// `ONE_CRYPTO_TLS_SET_CA_CERTIFICATE`.
    pub tls_set_ca_certificate:
        Option<unsafe extern "efiapi" fn(tls: *mut c_void, data: *mut c_void, data_size: usize) -> efi::Status>,
    /// Loads the local public certificate into the specified TLS object.
    ///
    /// `ONE_CRYPTO_TLS_SET_HOST_PUBLIC_CERT`.
    pub tls_set_host_public_cert:
        Option<unsafe extern "efiapi" fn(tls: *mut c_void, data: *mut c_void, data_size: usize) -> efi::Status>,
    /// Adds the local private key to the specified TLS object.
    ///
    /// `ONE_CRYPTO_TLS_SET_HOST_PRIVATE_KEY_EX`.
    pub tls_set_host_private_key_ex: Option<
        unsafe extern "efiapi" fn(
            tls: *mut c_void,
            data: *mut c_void,
            data_size: usize,
            password: *mut c_void,
        ) -> efi::Status,
    >,
    /// Adds the local private key to the specified TLS object.
    ///
    /// `ONE_CRYPTO_TLS_SET_HOST_PRIVATE_KEY`.
    pub tls_set_host_private_key:
        Option<unsafe extern "efiapi" fn(tls: *mut c_void, data: *mut c_void, data_size: usize) -> efi::Status>,
    /// Adds the CA-supplied certificate revocation list for certificate validation.
    ///
    /// `ONE_CRYPTO_TLS_SET_CERT_REVOCATION_LIST`.
    pub tls_set_cert_revocation_list:
        Option<unsafe extern "efiapi" fn(data: *mut c_void, data_size: usize) -> efi::Status>,
    /// Set the signature algorithm list to used by the TLS object.
    ///
    /// `ONE_CRYPTO_TLS_SET_SIGNATURE_ALGO_LIST`.
    pub tls_set_signature_algo_list:
        Option<unsafe extern "efiapi" fn(tls: *mut c_void, data: *mut u8, data_size: usize) -> efi::Status>,
    /// Set the EC curve to be used for TLS flows
    ///
    /// `ONE_CRYPTO_TLS_SET_EC_CURVE`.
    pub tls_set_ec_curve:
        Option<unsafe extern "efiapi" fn(tls: *mut c_void, data: *mut u8, data_size: usize) -> efi::Status>,
    /// Gets the protocol version used by the specified TLS connection.
    ///
    /// `ONE_CRYPTO_TLS_GET_VERSION`.
    pub tls_get_version: Option<unsafe extern "efiapi" fn(tls: *mut c_void) -> u16>,
    /// Gets the connection end of the specified TLS connection.
    ///
    /// `ONE_CRYPTO_TLS_GET_CONNECTION_END`.
    pub tls_get_connection_end: Option<unsafe extern "efiapi" fn(tls: *mut c_void) -> u8>,
    /// Gets the cipher suite used by the specified TLS connection.
    ///
    /// `ONE_CRYPTO_TLS_GET_CURRENT_CIPHER`.
    pub tls_get_current_cipher: Option<unsafe extern "efiapi" fn(tls: *mut c_void, cipher_id: *mut u16) -> efi::Status>,
    /// Gets the compression methods used by the specified TLS connection.
    ///
    /// `ONE_CRYPTO_TLS_GET_CURRENT_COMPRESSION_ID`.
    pub tls_get_current_compression_id:
        Option<unsafe extern "efiapi" fn(tls: *mut c_void, compression_id: *mut u8) -> efi::Status>,
    /// Gets the verification mode currently set in the TLS connection.
    ///
    /// `ONE_CRYPTO_TLS_GET_VERIFY`.
    pub tls_get_verify: Option<unsafe extern "efiapi" fn(tls: *mut c_void) -> u32>,
    /// Gets the session ID used by the specified TLS connection.
    ///
    /// `ONE_CRYPTO_TLS_GET_SESSION_ID`.
    pub tls_get_session_id: Option<
        unsafe extern "efiapi" fn(tls: *mut c_void, session_id: *mut u8, session_id_len: *mut u16) -> efi::Status,
    >,
    /// Gets the client random data used in the specified TLS connection.
    ///
    /// `ONE_CRYPTO_TLS_GET_CLIENT_RANDOM`.
    pub tls_get_client_random: Option<unsafe extern "efiapi" fn(tls: *mut c_void, client_random: *mut u8)>,
    /// Gets the server random data used in the specified TLS connection.
    ///
    /// `ONE_CRYPTO_TLS_GET_SERVER_RANDOM`.
    pub tls_get_server_random: Option<unsafe extern "efiapi" fn(tls: *mut c_void, server_random: *mut u8)>,
    /// Gets the master key data used in the specified TLS connection.
    ///
    /// `ONE_CRYPTO_TLS_GET_KEY_MATERIAL`.
    pub tls_get_key_material: Option<unsafe extern "efiapi" fn(tls: *mut c_void, key_material: *mut u8) -> efi::Status>,
    /// Gets the CA Certificate from the cert store.
    ///
    /// `ONE_CRYPTO_TLS_GET_CA_CERTIFICATE`.
    pub tls_get_ca_certificate:
        Option<unsafe extern "efiapi" fn(tls: *mut c_void, data: *mut c_void, data_size: *mut usize) -> efi::Status>,
    /// Gets the local public Certificate set in the specified TLS object.
    ///
    /// `ONE_CRYPTO_TLS_GET_HOST_PUBLIC_CERT`.
    pub tls_get_host_public_cert:
        Option<unsafe extern "efiapi" fn(tls: *mut c_void, data: *mut c_void, data_size: *mut usize) -> efi::Status>,
    /// Gets the local private key set in the specified TLS object.
    ///
    /// `ONE_CRYPTO_TLS_GET_HOST_PRIVATE_KEY`.
    pub tls_get_host_private_key:
        Option<unsafe extern "efiapi" fn(tls: *mut c_void, data: *mut c_void, data_size: *mut usize) -> efi::Status>,
    /// Gets the CA-supplied certificate revocation list data set in the specified TLS object.
    ///
    /// `ONE_CRYPTO_TLS_GET_CERT_REVOCATION_LIST`.
    pub tls_get_cert_revocation_list:
        Option<unsafe extern "efiapi" fn(data: *mut c_void, data_size: *mut usize) -> efi::Status>,
    /// Derive keying material from a TLS connection.
    ///
    /// `ONE_CRYPTO_TLS_GET_EXPORT_KEY`.
    pub tls_get_export_key: Option<
        unsafe extern "efiapi" fn(
            tls: *mut c_void,
            label: *const c_void,
            context: *const c_void,
            context_len: usize,
            key_buffer: *mut c_void,
            key_buffer_len: usize,
        ) -> efi::Status,
    >,
    /// `ONE_CRYPTO_IMAGE_TIMESTAMP_VERIFY`.
    pub image_timestamp_verify: Option<
        unsafe extern "efiapi" fn(
            auth_data: *const u8,
            data_size: usize,
            tsa_cert: *const u8,
            cert_size: usize,
            signing_time: *mut efi::Time,
        ) -> efi::Boolean,
    >,
    /// `ONE_CRYPTO_GET_CRYPTO_PROVIDER_VERSION_STRING`.
    pub get_crypto_provider_version_string:
        Option<unsafe extern "efiapi" fn(buffer: *mut u8, buffer_size: *mut usize) -> efi::Status>,
}

/// The functions appended to `ONE_CRYPTO_PROTOCOL` in version 2.0.
#[repr(C)]
#[derive(Default)]
#[allow(clippy::type_complexity)]
pub struct OneCryptoProtocolV2Extension {
    /// Locate, in a PKCS#7 SignedData blob, the X.509 certificate whose TBSCertificate digest matches a caller-supplied hash, and return that certificate as a newly allocated DER-encoded buffer.
    ///
    /// `ONE_CRYPTO_GET_TRUST_ANCHOR_X509_FROM_AUTH_DATA`.
    pub get_trust_anchor_x509_from_auth_data: Option<
        unsafe extern "efiapi" fn(
            cache_handle: *mut *mut c_void,
            tbs_cert_hash: *const u8,
            tbs_cert_hash_size: usize,
            auth_data: *const u8,
            auth_data_size: usize,
            trust_anchor_x509: *mut *mut u8,
            trust_anchor_x509_size: *mut usize,
        ) -> efi::Status,
    >,
    /// Release a trust-anchor cache previously allocated by ONE_CRYPTO_GET_TRUST_ANCHOR_X509_FROM_AUTH_DATA.
    ///
    /// `ONE_CRYPTO_FREE_TRUST_ANCHOR_X509_CACHE`.
    pub free_trust_anchor_x509_cache: Option<unsafe extern "efiapi" fn(cache_handle: *mut c_void)>,
    /// Determine the image-hash algorithm used by an Authenticode signature.
    ///
    /// `ONE_CRYPTO_GET_AUTHENTICODE_HASH_ALGORITHM`.
    pub get_authenticode_hash_algorithm: Option<
        unsafe extern "efiapi" fn(
            auth_data: *const u8,
            auth_data_size: usize,
            hash_type: *mut efi::Guid,
        ) -> efi::Status,
    >,
    /// AuthenticodeVerifyEx protocol prototype - verify a PE/COFF Authenticode signature and optionally return the verified signer chain.
    ///
    /// `ONE_CRYPTO_AUTHENTICODE_VERIFY_EX`.
    pub authenticode_verify_ex: Option<
        unsafe extern "efiapi" fn(
            auth_data: *const u8,
            data_size: usize,
            trusted_cert: *const u8,
            cert_size: usize,
            image_hash: *const u8,
            hash_size: usize,
            cert_chain: *mut *mut u8,
            cert_chain_size: *mut usize,
        ) -> efi::Status,
    >,
    /// Compute the digest of a buffer using a generic hash-algorithm GUID.
    ///
    /// `ONE_CRYPTO_HASH_ALL_BY_GUID`.
    pub hash_all_by_guid: Option<
        unsafe extern "efiapi" fn(
            hash_type: *const efi::Guid,
            buffer: *const c_void,
            buffer_size: usize,
            digest: *mut u8,
            digest_size: *mut usize,
        ) -> efi::Status,
    >,
    /// `ONE_CRYPTO_CMS_GET_SIGNER_INFO_NUM`.
    pub cms_get_signer_info_num: Option<unsafe extern "efiapi" fn(p7_data: *const u8, p7_length: usize) -> usize>,
    /// Verify a PKCS#7/CMS SignedData structure and optionally return the verified signer certificate chain in EFI_CERT_STACK form.
    ///
    /// `ONE_CRYPTO_CMS_VERIFY`.
    pub cms_verify: Option<
        unsafe extern "efiapi" fn(
            p7_data: *const u8,
            p7_length: usize,
            trusted_cert: *const u8,
            cert_length: usize,
            in_data: *const u8,
            data_length: usize,
            signer_chain: *mut *mut u8,
            signer_chain_size: *mut usize,
        ) -> efi::Boolean,
    >,
    /// Query algorithms supported by an ECIT crypto operation.
    ///
    /// `ONE_CRYPTO_GET_CRYPTO_OP_CAPABILITY`.
    pub get_crypto_op_capability: Option<
        unsafe extern "efiapi" fn(
            op_id_guid: *const efi::Guid,
            capabilities: *mut *mut BaseCryptOpCapability,
            capability_count: *mut usize,
        ) -> efi::Status,
    >,
    /// `ONE_CRYPTO_X509_IS_PUBLIC_KEY_SUPPORTED`.
    pub x509_is_public_key_supported:
        Option<unsafe extern "efiapi" fn(cert: *const u8, cert_size: usize) -> efi::Boolean>,
}

/// `ONE_CRYPTO_PROTOCOL` version 2.0.
#[repr(C)]
#[derive(Default)]
pub struct OneCryptoProtocolV2 {
    /// The version 1.0 table.
    pub base: OneCryptoProtocol,
    /// The functions added in version 2.0.
    pub v2: OneCryptoProtocolV2Extension,
}

/// `gOneCryptoProtocolGuid`.
const ONE_CRYPTO_PROTOCOL_GUID: BinaryGuid = BinaryGuid::from_string("c1012170-e2d0-460c-95d8-76385a3957e7");

// The version 1.0 table holds the version fields and 213 function pointers, and version 2.0 appends its functions
// directly after it.
const _: () = assert!(size_of::<OneCryptoProtocol>() == size_of::<usize>() * 214);
const _: () = assert!(core::mem::offset_of!(OneCryptoProtocolV2, v2) == size_of::<OneCryptoProtocol>());

// SAFETY: `OneCryptoProtocol` is `#[repr(C)]` and matches the version 1.0 `ONE_CRYPTO_PROTOCOL` layout identified by
// `gOneCryptoProtocolGuid`. Every compatible provider's table starts with this layout.
unsafe impl ProtocolInterface for OneCryptoProtocol {
    const PROTOCOL_GUID: BinaryGuid = ONE_CRYPTO_PROTOCOL_GUID;
}

// SAFETY: `OneCryptoProtocolV2` is `#[repr(C)]` and matches the version 2.0 `ONE_CRYPTO_PROTOCOL` layout identified by
// `gOneCryptoProtocolGuid`. It must only be located after checking that the provider reports major version 2 or later.
unsafe impl ProtocolInterface for OneCryptoProtocolV2 {
    const PROTOCOL_GUID: BinaryGuid = ONE_CRYPTO_PROTOCOL_GUID;
}

impl OneCryptoProtocol {
    /// Returns `true` if this protocol instance is compatible with these bindings.
    ///
    /// Any minor version is accepted, because minor versions only append functions these bindings do not use.
    pub fn is_compatible(&self) -> bool {
        (ONE_CRYPTO_VERSION_MAJOR_MIN..=ONE_CRYPTO_VERSION_MAJOR).contains(&self.major)
    }

    /// Returns `true` if the provider implements the [`OneCryptoProtocolV2`] table.
    pub fn has_v2(&self) -> bool {
        self.major >= 2
    }
}
