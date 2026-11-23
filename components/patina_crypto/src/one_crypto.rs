//! Crypto services backed by the `OneCrypto` protocol.
//!
//! [`OneCrypto`] implements every service in [`crate::service`] by calling into a [`OneCryptoProtocol`] instance
//! produced by a `OneCrypto` provider driver. It follows the same contract as `BaseCryptLibOnOneCrypto` in
//! `mu_basecore`:
//!
//! - The protocol major version must be between [`ONE_CRYPTO_VERSION_MAJOR_MIN`] and [`ONE_CRYPTO_VERSION_MAJOR`].
//!   Functions added in version 2.0 ([`OneCryptoProtocolV2Extension`](protocol::OneCryptoProtocolV2Extension)) are
//!   reported as [`CryptoError::Unsupported`] by version 1 providers, unless a version 1 equivalent exists.
//! - A `NULL` function pointer means the provider does not support that function, which is reported as
//!   [`CryptoError::Unsupported`].
//! - Buffers returned by the provider are copied into Rust-owned memory and released with the function documented
//!   by the protocol (`FreePool()`, `Pkcs7FreeSigners()`, or `X509StackFree()`).
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
mod aes;
mod authenticode;
mod ec;
mod encryption;
mod hash;
mod kdf;
mod pkcs7;
pub mod protocol;
mod random;
mod rsa;
mod signature;
mod x509;

use alloc::{string::String, vec, vec::Vec};
use core::{ffi::c_void, ptr::NonNull};

use patina::{
    component::{
        protocol::Protocol,
        service::{
            IntoService, Service,
            compat_memory::{CompatMemoryManager, PoolAllocation},
        },
    },
    standard::efi,
};
use zerocopy::IntoBytes;

use crate::{
    error::{CryptoError, Result},
    service::{encryption::Encryption, hash::Hash, random::Random, signature::Signature},
};

use protocol::{
    ONE_CRYPTO_VERSION_MAJOR, ONE_CRYPTO_VERSION_MAJOR_MIN, OneCryptoProtocol, OneCryptoProtocolV2,
    OneCryptoProtocolV2Extension,
};

/// Returns the function pointer `$name` from the protocol, or [`CryptoError::Unsupported`] if it is `NULL`.
macro_rules! protocol_fn {
    ($crypto:expr, $name:ident) => {
        $crypto.protocol().$name.ok_or($crate::error::CryptoError::Unsupported)?
    };
}
pub(crate) use protocol_fn;

/// Returns the version 2.0 function pointer `$name` from the protocol, or [`CryptoError::Unsupported`] if the
/// provider implements version 1 or the pointer is `NULL`.
macro_rules! protocol_v2_fn {
    ($crypto:expr, $name:ident) => {
        $crypto.protocol_v2().and_then(|v2| v2.$name).ok_or($crate::error::CryptoError::Unsupported)?
    };
}
pub(crate) use protocol_v2_fn;

/// The crypto services backed by the `OneCrypto` protocol.
///
/// Produced by [`OneCryptoComponent`](crate::component::OneCryptoComponent).
#[derive(IntoService, Clone, Copy)]
#[service(dyn Encryption, dyn Hash, dyn Random, dyn Signature)]
pub struct OneCrypto {
    protocol: Protocol<OneCryptoProtocol>,
    /// The version 2.0 table, present only if the provider reports major version 2 or later.
    protocol_v2: Option<Protocol<OneCryptoProtocolV2>>,
    memory: Service<dyn CompatMemoryManager>,
}

impl OneCrypto {
    /// Creates the crypto services for `protocol`.
    ///
    /// `protocol_v2` resolves the same protocol instance as the version 2.0 table. It is only dereferenced if
    /// `protocol` reports major version 2 or later. `memory` frees the buffers the provider returns with `FreePool()`.
    ///
    /// # Errors
    ///
    /// Returns [`CryptoError::Unsupported`] if the protocol version is not compatible.
    pub fn new(
        protocol: Protocol<OneCryptoProtocol>,
        protocol_v2: Protocol<OneCryptoProtocolV2>,
        memory: Service<dyn CompatMemoryManager>,
    ) -> Result<Self> {
        if !protocol.is_compatible() {
            log::error!(
                "OneCrypto protocol version {}.{} is not supported; supported major versions are {}-{}",
                protocol.major,
                protocol.minor,
                ONE_CRYPTO_VERSION_MAJOR_MIN,
                ONE_CRYPTO_VERSION_MAJOR
            );
            return Err(CryptoError::Unsupported);
        }
        let protocol_v2 = protocol.has_v2().then_some(protocol_v2);
        Ok(Self { protocol, protocol_v2, memory })
    }

    pub(crate) fn protocol(&self) -> &OneCryptoProtocol {
        &self.protocol
    }

    /// Returns the functions added in version 2.0, or `None` if the provider implements version 1.
    pub(crate) fn protocol_v2(&self) -> Option<&OneCryptoProtocolV2Extension> {
        self.protocol_v2.as_ref().map(|protocol| &protocol.v2)
    }

    /// Copies a provider buffer allocated with `AllocatePool()` and frees it with `FreePool()`.
    ///
    /// Returns an empty buffer if `data` is null.
    ///
    /// # Safety
    ///
    /// `data` must be null, or a not-yet-freed UEFI pool allocation readable for `len` bytes.
    pub(crate) unsafe fn take_pool(&self, data: *mut u8, len: usize) -> Vec<u8> {
        // SAFETY: The caller guarantees `data` is null or a not-yet-freed pool allocation.
        let Some(allocation) = (unsafe { self.pool(data) }) else {
            return Vec::new();
        };
        // SAFETY: The caller guarantees `data` is readable for `len` bytes. The slice is copied before the
        // allocation is freed.
        unsafe { core::slice::from_raw_parts(allocation.as_ptr().as_ptr(), len) }.to_vec()
    }

    /// Wraps a provider buffer allocated with `AllocatePool()` so it is freed with `FreePool()` on drop.
    ///
    /// Returns `None` if `data` is null.
    ///
    /// # Safety
    ///
    /// `data` must be null or a not-yet-freed UEFI pool allocation.
    pub(crate) unsafe fn pool(&self, data: *mut u8) -> Option<PoolAllocation> {
        // SAFETY: The caller guarantees `data` is a not-yet-freed pool allocation.
        NonNull::new(data).map(|data| unsafe { PoolAllocation::new(data, *self.memory) })
    }
}

/// An 8-byte aligned, caller-allocated buffer that holds a provider context, such as a hash or AES context.
///
/// The buffer is accessed only through raw pointers, so the provider may update it through a shared reference.
pub(crate) struct ContextBuffer {
    buffer: NonNull<[u64]>,
}

impl ContextBuffer {
    /// Allocates a zeroed context buffer of at least `size` bytes.
    ///
    /// Returns [`CryptoError::Failed`] if `size` is zero.
    pub(crate) fn new(size: usize) -> Result<Self> {
        if size == 0 {
            return Err(CryptoError::Failed);
        }
        let buffer = vec![0u64; size.div_ceil(size_of::<u64>())].into_boxed_slice();
        Ok(Self { buffer: NonNull::from(alloc::boxed::Box::leak(buffer)) })
    }

    /// Returns the size of the buffer in bytes.
    pub(crate) fn len(&self) -> usize {
        self.buffer.len() * size_of::<u64>()
    }

    pub(crate) fn as_ptr(&self) -> *mut c_void {
        self.buffer.as_ptr().cast()
    }
}

impl Drop for ContextBuffer {
    fn drop(&mut self) {
        // SAFETY: `buffer` was leaked from a `Box<[u64]>` in `new` and is reclaimed exactly once.
        drop(unsafe { alloc::boxed::Box::from_raw(self.buffer.as_ptr()) });
    }
}

/// Copies provider-encoded bytes into an 8-byte aligned buffer so they can be passed back as a structure.
pub(crate) fn aligned_copy(bytes: &[u8]) -> Vec<u64> {
    let mut buffer = vec![0u64; bytes.len().div_ceil(size_of::<u64>()).max(1)];
    buffer.as_mut_bytes()[..bytes.len()].copy_from_slice(bytes);
    buffer
}

/// Converts a `BOOLEAN` provider result into a [`Result`], reporting `FALSE` as [`CryptoError::Failed`].
pub(crate) fn ensure(result: efi::Boolean) -> Result<()> {
    ensure_or(result, CryptoError::Failed)
}

/// Converts a `BOOLEAN` provider result into a [`Result`], reporting `FALSE` as `error`.
pub(crate) fn ensure_or(result: efi::Boolean, error: CryptoError) -> Result<()> {
    if result.into() { Ok(()) } else { Err(error) }
}

/// Converts an `EFI_STATUS` or `RETURN_STATUS` provider result into a [`Result`].
pub(crate) fn status_to_result(status: efi::Status) -> Result<()> {
    match status {
        efi::Status::SUCCESS => Ok(()),
        efi::Status::INVALID_PARAMETER | efi::Status::BUFFER_TOO_SMALL => Err(CryptoError::InvalidParameter),
        efi::Status::UNSUPPORTED => Err(CryptoError::Unsupported),
        efi::Status::NOT_FOUND => Err(CryptoError::NotFound),
        efi::Status::SECURITY_VIOLATION => Err(CryptoError::VerificationFailed),
        efi::Status::OUT_OF_RESOURCES => Err(CryptoError::OutOfResources),
        _ => Err(CryptoError::Failed),
    }
}

/// Converts an optional slice into the pointer and length a provider expects, using null for `None`.
pub(crate) fn optional_slice(data: Option<&[u8]>) -> (*const u8, usize) {
    data.map_or((core::ptr::null(), 0), |data| (data.as_ptr(), data.len()))
}

/// Returns `value` as a NUL-terminated C string.
///
/// # Errors
///
/// Returns [`CryptoError::InvalidParameter`] if `value` contains a NUL byte.
pub(crate) fn c_string(value: &str) -> Result<Vec<u8>> {
    if value.as_bytes().contains(&0) {
        return Err(CryptoError::InvalidParameter);
    }
    let mut string = Vec::with_capacity(value.len() + 1);
    string.extend_from_slice(value.as_bytes());
    string.push(0);
    Ok(string)
}

/// Returns a pointer to the optional NUL-terminated C string, using null for `None`.
pub(crate) fn optional_c_string_ptr(value: &Option<Vec<u8>>) -> *const u8 {
    value.as_ref().map_or(core::ptr::null(), |value| value.as_ptr())
}

/// Converts a NUL-terminated byte buffer returned by the provider into a [`String`].
pub(crate) fn string_from_c(mut bytes: Vec<u8>) -> Result<String> {
    if let Some(end) = bytes.iter().position(|&b| b == 0) {
        bytes.truncate(end);
    }
    String::from_utf8(bytes).map_err(|_| CryptoError::Failed)
}

/// Calls a provider function that writes a variable-sized output into a caller buffer.
///
/// `fill` receives the buffer and its size. It must update the size to the number of bytes written on success, or
/// to the required size if the buffer is too small. The buffer is 8-byte aligned so it can hold provider structures.
///
/// Returns the size reported by the provider when it fails.
pub(crate) fn try_output_buffer(
    initial_size: usize,
    mut fill: impl FnMut(*mut u8, &mut usize) -> efi::Boolean,
) -> core::result::Result<Vec<u8>, usize> {
    let mut capacity = initial_size.max(1);
    // A provider that reports a larger size is given exactly one retry.
    for _ in 0..2 {
        let mut buffer = vec![0u64; capacity.div_ceil(size_of::<u64>())];
        let bytes = buffer.as_mut_bytes();
        let mut size = capacity;
        if fill(bytes.as_mut_ptr(), &mut size).into() {
            return Ok(bytes[..size.min(capacity)].to_vec());
        }
        if size <= capacity {
            return Err(size);
        }
        capacity = size;
    }
    Err(capacity)
}

/// Same as [`try_output_buffer`], reporting failure as [`CryptoError::Failed`].
pub(crate) fn output_buffer(
    initial_size: usize,
    fill: impl FnMut(*mut u8, &mut usize) -> efi::Boolean,
) -> Result<Vec<u8>> {
    try_output_buffer(initial_size, fill).map_err(|_| CryptoError::Failed)
}

/// Calls a provider function that follows the `RETURN_BUFFER_TOO_SMALL` size query protocol and returns a string.
pub(crate) fn status_string(mut fill: impl FnMut(*mut u8, &mut usize) -> efi::Status) -> Result<String> {
    let mut size = 0;
    match fill(core::ptr::null_mut(), &mut size) {
        efi::Status::BUFFER_TOO_SMALL => {}
        efi::Status::SUCCESS => return Ok(String::new()),
        status => return status_to_result(status).map(|_| String::new()),
    }
    let mut buffer = vec![0u8; size];
    status_to_result(fill(buffer.as_mut_ptr(), &mut size))?;
    buffer.truncate(size);
    string_from_c(buffer)
}

/// Parses an `EFI_CERT_STACK` into its DER-encoded certificates.
///
/// The format is a `UINT8` certificate count followed by each certificate as a little-endian `UINT32` length and
/// its DER bytes, without padding.
pub(crate) fn parse_cert_stack(stack: &[u8]) -> Result<Vec<Vec<u8>>> {
    let Some((&count, mut rest)) = stack.split_first() else {
        return Ok(Vec::new());
    };
    let mut certificates = Vec::with_capacity(usize::from(count));
    for _ in 0..count {
        let (length, remaining) = rest.split_first_chunk::<4>().ok_or(CryptoError::Failed)?;
        let length = usize::try_from(u32::from_le_bytes(*length)).map_err(|_| CryptoError::Failed)?;
        let (certificate, remaining) = remaining.split_at_checked(length).ok_or(CryptoError::Failed)?;
        certificates.push(certificate.to_vec());
        rest = remaining;
    }
    Ok(certificates)
}

/// Returns the sub-slice of `source` at `data..data + len`, or `None` if it is not fully contained in `source`.
pub(crate) fn subslice_of(source: &[u8], data: *const u8, len: usize) -> Option<&[u8]> {
    let offset = data.addr().checked_sub(source.as_ptr().addr())?;
    source.get(offset..offset.checked_add(len)?)
}

/// An opaque provider context pointer that is freed on drop.
pub(crate) struct ProviderContext {
    context: NonNull<c_void>,
    free: unsafe extern "efiapi" fn(*mut c_void),
}

impl ProviderContext {
    /// Wraps a context returned by the provider.
    ///
    /// Returns [`CryptoError::OutOfResources`] if `context` is null.
    ///
    /// # Safety
    ///
    /// `context` must be null or a context allocated by the provider that `free` releases.
    pub(crate) unsafe fn new(context: *mut c_void, free: unsafe extern "efiapi" fn(*mut c_void)) -> Result<Self> {
        let context = NonNull::new(context).ok_or(CryptoError::OutOfResources)?;
        Ok(Self { context, free })
    }

    pub(crate) fn as_ptr(&self) -> *mut c_void {
        self.context.as_ptr()
    }
}

impl Drop for ProviderContext {
    fn drop(&mut self) {
        // SAFETY: `context` was allocated by the provider and is released exactly once by the matching `free`.
        unsafe { (self.free)(self.context.as_ptr()) }
    }
}

/// A provider `STACK_OF(X509)` built from DER-encoded certificates and freed with `X509StackFree()`.
pub(crate) struct X509Stack {
    stack: *mut u8,
    free: unsafe extern "efiapi" fn(*mut c_void),
}

impl X509Stack {
    /// Builds a stack containing `certificates`.
    pub(crate) fn new(crypto: &OneCrypto, certificates: &[&[u8]]) -> Result<Self> {
        let mut stack = Self { stack: core::ptr::null_mut(), free: protocol_fn!(crypto, x509_stack_free) };
        for certificate in certificates {
            let construct = protocol_fn!(crypto, x509_construct_certificate_stack);
            // SAFETY: The variadic arguments are a single (UINT8 *, UINTN) certificate pair followed by the NULL
            // terminator, as required by `X509ConstructCertificateStack`. The certificate is valid for the call.
            ensure(unsafe {
                construct(&mut stack.stack, certificate.as_ptr(), certificate.len(), core::ptr::null::<u8>())
            })?;
        }
        Ok(stack)
    }

    pub(crate) fn as_ptr(&self) -> *mut u8 {
        self.stack
    }
}

impl Drop for X509Stack {
    fn drop(&mut self) {
        if !self.stack.is_null() {
            // SAFETY: `stack` was created by `X509ConstructCertificateStack` and is released exactly once.
            unsafe { (self.free)(self.stack.cast()) }
        }
    }
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
pub(crate) mod test_support {
    //! Shared helpers for testing the `OneCrypto` services against a fake protocol.
    use alloc::boxed::Box;

    use patina::component::service::compat_memory::MockCompatMemoryManager;

    use super::*;

    /// Returns a version 2.0 protocol with no functions, for tests to fill in.
    pub(crate) fn protocol() -> OneCryptoProtocol {
        OneCryptoProtocol { major: ONE_CRYPTO_VERSION_MAJOR, minor: 0, ..Default::default() }
    }

    /// Returns a version 2.0 protocol with `base` and `v2` functions, for tests that need version 2.0 functions.
    pub(crate) fn protocol_v2(base: OneCryptoProtocol, v2: OneCryptoProtocolV2Extension) -> OneCryptoProtocolV2 {
        OneCryptoProtocolV2 { base, v2 }
    }

    impl From<OneCryptoProtocol> for OneCryptoProtocolV2 {
        fn from(base: OneCryptoProtocol) -> Self {
            Self { base, v2: Default::default() }
        }
    }

    /// Creates [`OneCrypto`] for `protocol` with a memory manager that expects `frees` calls to `free_pool`.
    pub(crate) fn crypto_with_frees(protocol: impl Into<OneCryptoProtocolV2>, frees: usize) -> OneCrypto {
        let mut memory = MockCompatMemoryManager::new();
        memory.expect_free_pool().times(frees).returning(|address| {
            // SAFETY: Tests only hand out pool buffers leaked from `pool_buffer`.
            drop(unsafe { Box::from_raw(core::ptr::slice_from_raw_parts_mut(address as *mut u8, POOL_SIZE)) });
            Ok(())
        });
        let memory = Service::mock(Box::new(memory) as Box<dyn CompatMemoryManager>);
        let (protocol, protocol_v2) = mock_protocol(protocol);
        OneCrypto::new(protocol, protocol_v2, memory).expect("compatible protocol")
    }

    /// Returns [`Protocol`]s that resolve to the version 1.0 and 2.0 views of a leaked copy of `protocol`.
    pub(crate) fn mock_protocol(
        protocol: impl Into<OneCryptoProtocolV2>,
    ) -> (Protocol<OneCryptoProtocol>, Protocol<OneCryptoProtocolV2>) {
        let protocol: &'static OneCryptoProtocolV2 = Box::leak(Box::new(protocol.into()));
        (Protocol::mock(&protocol.base), Protocol::mock(protocol))
    }

    /// Creates [`OneCrypto`] for `protocol` that does not expect any pool frees.
    pub(crate) fn crypto(protocol: impl Into<OneCryptoProtocolV2>) -> OneCrypto {
        crypto_with_frees(protocol, 0)
    }

    const POOL_SIZE: usize = 256;

    /// Returns a leaked buffer holding `data`, standing in for a provider pool allocation.
    pub(crate) fn pool_buffer(data: &[u8]) -> *mut u8 {
        assert!(data.len() <= POOL_SIZE);
        let mut buffer = Box::new([0u8; POOL_SIZE]);
        buffer[..data.len()].copy_from_slice(data);
        Box::into_raw(buffer).cast()
    }

    /// Converts a Rust `bool` into a provider `BOOLEAN`.
    pub(crate) fn boolean(value: bool) -> efi::Boolean {
        value.into()
    }

    /// Copies `data` into a provider output buffer, following the size query protocol.
    ///
    /// # Safety
    ///
    /// `buffer` must be writable for `*size` bytes and `size` must be valid.
    pub(crate) unsafe fn write_output(data: &[u8], buffer: *mut u8, size: *mut usize) -> efi::Boolean {
        // SAFETY: The caller guarantees `size` is valid.
        let size = unsafe { &mut *size };
        if buffer.is_null() || *size < data.len() {
            *size = data.len();
            return boolean(false);
        }
        // SAFETY: The caller guarantees `buffer` is writable for `*size >= data.len()` bytes.
        unsafe { core::ptr::copy_nonoverlapping(data.as_ptr(), buffer, data.len()) };
        *size = data.len();
        boolean(true)
    }

    /// Returns the bytes of `data..data + len`.
    ///
    /// # Safety
    ///
    /// `data` must be readable for `len` bytes.
    pub(crate) unsafe fn input<'a>(data: *const u8, len: usize) -> &'a [u8] {
        if len == 0 {
            return &[];
        }
        // SAFETY: The caller guarantees `data` is readable for `len` bytes.
        unsafe { core::slice::from_raw_parts(data, len) }
    }
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
mod tests {
    use alloc::boxed::Box;

    use patina::component::service::compat_memory::MockCompatMemoryManager;

    use super::{test_support::*, *};

    #[test]
    fn test_one_crypto_context_buffer_and_aligned_copy() {
        assert!(ContextBuffer::new(0).is_err());
        let buffer = ContextBuffer::new(9).expect("buffer");
        assert_eq!(buffer.len(), 16);
        assert_eq!(buffer.as_ptr().align_offset(align_of::<u64>()), 0);

        assert_eq!(aligned_copy(&[]), [0]);
        let copy = aligned_copy(&[1, 2, 3, 4, 5, 6, 7, 8, 9]);
        assert_eq!(copy.len(), 2);
        assert_eq!(&copy.as_bytes()[..10], &[1, 2, 3, 4, 5, 6, 7, 8, 9, 0]);
    }

    #[test]
    fn test_one_crypto_rejects_incompatible_versions() {
        let memory = Service::mock(Box::new(MockCompatMemoryManager::new()) as Box<dyn CompatMemoryManager>);
        for (major, minor) in [(ONE_CRYPTO_VERSION_MAJOR + 1, 0), (ONE_CRYPTO_VERSION_MAJOR_MIN - 1, u16::MAX)] {
            let (protocol, protocol_v2) = mock_protocol(OneCryptoProtocol { major, minor, ..Default::default() });
            assert_eq!(OneCrypto::new(protocol, protocol_v2, memory).err(), Some(CryptoError::Unsupported));
        }
    }

    #[test]
    fn test_one_crypto_accepts_v1_and_v2() {
        let memory = Service::mock(Box::new(MockCompatMemoryManager::new()) as Box<dyn CompatMemoryManager>);
        for (major, minor, has_v2) in [(1, 0, false), (1, 7, false), (2, 0, true), (2, 3, true)] {
            let (protocol, protocol_v2) = mock_protocol(OneCryptoProtocol { major, minor, ..Default::default() });
            let crypto = OneCrypto::new(protocol, protocol_v2, memory).expect("compatible protocol");
            assert_eq!(crypto.protocol_v2().is_some(), has_v2);
        }
    }

    #[test]
    fn test_one_crypto_status_to_result() {
        assert_eq!(status_to_result(efi::Status::SUCCESS), Ok(()));
        assert_eq!(status_to_result(efi::Status::INVALID_PARAMETER), Err(CryptoError::InvalidParameter));
        assert_eq!(status_to_result(efi::Status::BUFFER_TOO_SMALL), Err(CryptoError::InvalidParameter));
        assert_eq!(status_to_result(efi::Status::UNSUPPORTED), Err(CryptoError::Unsupported));
        assert_eq!(status_to_result(efi::Status::NOT_FOUND), Err(CryptoError::NotFound));
        assert_eq!(status_to_result(efi::Status::SECURITY_VIOLATION), Err(CryptoError::VerificationFailed));
        assert_eq!(status_to_result(efi::Status::OUT_OF_RESOURCES), Err(CryptoError::OutOfResources));
        assert_eq!(status_to_result(efi::Status::DEVICE_ERROR), Err(CryptoError::Failed));
    }

    #[test]
    fn test_one_crypto_c_string() {
        assert_eq!(c_string("abc"), Ok(b"abc\0".to_vec()));
        assert_eq!(c_string("a\0c"), Err(CryptoError::InvalidParameter));
        assert!(optional_c_string_ptr(&None).is_null());
        assert_eq!(string_from_c(b"name\0junk".to_vec()), Ok(String::from("name")));
        assert_eq!(string_from_c(alloc::vec![0xff]), Err(CryptoError::Failed));
    }

    #[test]
    fn test_one_crypto_output_buffer_retries_once_with_the_required_size() {
        let data = [7u8; 40];
        let mut calls = 0;
        let output = output_buffer(4, |buffer, size| {
            calls += 1;
            // SAFETY: `output_buffer` passes a buffer writable for `*size` bytes.
            unsafe { write_output(&data, buffer, size) }
        });
        assert_eq!(output, Ok(data.to_vec()));
        assert_eq!(calls, 2);

        assert_eq!(
            try_output_buffer(4, |_, size| {
                *size = 2;
                boolean(false)
            }),
            Err(2)
        );
        assert_eq!(
            output_buffer(4, |_, size| {
                *size += 1;
                boolean(false)
            }),
            Err(CryptoError::Failed)
        );
    }

    #[test]
    fn test_one_crypto_status_string() {
        let value = b"provider 1.0\0";
        let string = status_string(|buffer, size| {
            if buffer.is_null() {
                *size = value.len();
                return efi::Status::BUFFER_TOO_SMALL;
            }
            // SAFETY: `status_string` passes a buffer writable for `*size` bytes.
            unsafe { core::ptr::copy_nonoverlapping(value.as_ptr(), buffer, value.len()) };
            efi::Status::SUCCESS
        });
        assert_eq!(string, Ok(String::from("provider 1.0")));
        assert_eq!(status_string(|_, _| efi::Status::SUCCESS), Ok(String::new()));
        assert_eq!(status_string(|_, _| efi::Status::NOT_FOUND), Err(CryptoError::NotFound));
    }

    #[test]
    fn test_one_crypto_parse_cert_stack() {
        assert_eq!(parse_cert_stack(&[]), Ok(Vec::new()));
        let stack = [2, 2, 0, 0, 0, 0xa, 0xb, 1, 0, 0, 0, 0xc];
        assert_eq!(parse_cert_stack(&stack), Ok(alloc::vec![alloc::vec![0xa, 0xb], alloc::vec![0xc]]));
        assert_eq!(parse_cert_stack(&stack[..stack.len() - 1]), Err(CryptoError::Failed));
        assert_eq!(parse_cert_stack(&[1, 0, 0]), Err(CryptoError::Failed));
    }

    #[test]
    fn test_one_crypto_subslice_of() {
        let source = [1u8, 2, 3, 4];
        assert_eq!(subslice_of(&source, source[1..].as_ptr(), 2), Some(&source[1..3]));
        assert_eq!(subslice_of(&source, source[1..].as_ptr(), 4), None);
        assert_eq!(subslice_of(&source[1..], source.as_ptr(), 1), None);
    }

    #[test]
    fn test_one_crypto_take_pool_copies_and_frees() {
        let crypto = crypto_with_frees(protocol(), 1);
        let data = pool_buffer(&[1, 2, 3]);
        // SAFETY: `data` is a test pool allocation readable for 3 bytes.
        assert_eq!(unsafe { crypto.take_pool(data, 3) }, alloc::vec![1, 2, 3]);
        // SAFETY: A null pointer is always accepted.
        assert!(unsafe { crypto.take_pool(core::ptr::null_mut(), 3) }.is_empty());
    }

    #[test]
    fn test_one_crypto_x509_stack_requires_construct_and_free() {
        let crypto = crypto(protocol());
        assert_eq!(X509Stack::new(&crypto, &[b"cert"]).err(), Some(CryptoError::Unsupported));
    }
}
