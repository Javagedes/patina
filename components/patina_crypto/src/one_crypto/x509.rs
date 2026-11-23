//! X.509 certificate operations used by the signature service.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use alloc::{string::String, vec, vec::Vec};
use core::{cmp::Ordering, ffi::c_void};

use patina::standard::efi;
use zerocopy::IntoBytes;

use super::{
    OneCrypto, aligned_copy, c_string, ensure, ensure_or, output_buffer, protocol_fn, status_string, subslice_of,
    try_output_buffer,
};
use crate::{
    error::{CryptoError, Result},
    service::signature::{X509DateTime, X509Validity},
};

/// The initial output buffer size for names and other certificate fields.
const X509_BUFFER_SIZE: usize = 256;
/// The initial buffer size for a provider date and time structure.
const DATE_TIME_SIZE: usize = 64;

type CertificateFieldFn = unsafe extern "efiapi" fn(*const u8, usize, *mut u8, *mut usize) -> efi::Boolean;

impl OneCrypto {
    /// Reads a variable-sized certificate field.
    fn certificate_field(&self, field: CertificateFieldFn, certificate: &[u8]) -> Result<Vec<u8>> {
        // SAFETY: `certificate` is valid for the call and `output_buffer` passes a buffer writable for `*size`
        // bytes.
        output_buffer(X509_BUFFER_SIZE, |buffer, size| unsafe {
            field(certificate.as_ptr(), certificate.len(), buffer, size)
        })
    }
}

impl OneCrypto {
    pub(super) fn subject_name(&self, certificate: &[u8]) -> Result<Vec<u8>> {
        self.certificate_field(protocol_fn!(self, x509_get_subject_name), certificate)
    }

    pub(super) fn issuer_name(&self, certificate: &[u8]) -> Result<Vec<u8>> {
        self.certificate_field(protocol_fn!(self, x509_get_issuer_name), certificate)
    }

    pub(super) fn common_name(&self, certificate: &[u8]) -> Result<String> {
        let get_common_name = protocol_fn!(self, x509_get_common_name);
        // SAFETY: `certificate` is valid for the call and `status_string` passes a null buffer or a buffer writable
        // for `*size` bytes.
        status_string(|buffer, size| unsafe { get_common_name(certificate.as_ptr(), certificate.len(), buffer, size) })
    }

    pub(super) fn organization_name(&self, certificate: &[u8]) -> Result<String> {
        let get_organization_name = protocol_fn!(self, x509_get_organization_name);
        // SAFETY: `certificate` is valid for the call and `status_string` passes a null buffer or a buffer writable
        // for `*size` bytes.
        status_string(|buffer, size| unsafe {
            get_organization_name(certificate.as_ptr(), certificate.len(), buffer, size)
        })
    }

    pub(super) fn certificate_version(&self, certificate: &[u8]) -> Result<usize> {
        let get_version = protocol_fn!(self, x509_get_version);
        let mut version = 0;
        // SAFETY: `certificate` is valid for the call.
        ensure(unsafe { get_version(certificate.as_ptr(), certificate.len(), &mut version) })?;
        Ok(version)
    }

    pub(super) fn serial_number(&self, certificate: &[u8]) -> Result<Vec<u8>> {
        self.certificate_field(protocol_fn!(self, x509_get_serial_number), certificate)
    }

    pub(super) fn certificate_signature_algorithm(&self, certificate: &[u8]) -> Result<Vec<u8>> {
        self.certificate_field(protocol_fn!(self, x509_get_signature_algorithm), certificate)
    }

    pub(super) fn tbs_certificate(&self, certificate: &[u8]) -> Result<Vec<u8>> {
        let get_tbs_cert = protocol_fn!(self, x509_get_tbs_cert);
        let mut tbs = core::ptr::null_mut();
        let mut tbs_size = 0;
        // SAFETY: `certificate` is valid for the call.
        ensure(unsafe { get_tbs_cert(certificate.as_ptr(), certificate.len(), &mut tbs, &mut tbs_size) })?;
        // Providers either return a pointer into the certificate or a new pool allocation.
        if let Some(tbs) = subslice_of(certificate, tbs, tbs_size) {
            return Ok(tbs.to_vec());
        }
        // SAFETY: A TBSCertificate outside the certificate is a pool allocation of `tbs_size` bytes owned by the
        // caller.
        Ok(unsafe { self.take_pool(tbs, tbs_size) })
    }

    pub(super) fn certificate_validity(&self, certificate: &[u8]) -> Result<X509Validity> {
        let get_validity = protocol_fn!(self, x509_get_validity);
        let (mut from_capacity, mut to_capacity) = (DATE_TIME_SIZE, DATE_TIME_SIZE);
        // A provider that reports larger sizes is given exactly one retry.
        for _ in 0..2 {
            let mut from = vec![0u64; from_capacity.div_ceil(size_of::<u64>())];
            let mut to = vec![0u64; to_capacity.div_ceil(size_of::<u64>())];
            let (mut from_size, mut to_size) = (from_capacity, to_capacity);
            // SAFETY: `certificate` is valid for the call and the buffers are 8-byte aligned and writable for their
            // sizes.
            let result = unsafe {
                get_validity(
                    certificate.as_ptr(),
                    certificate.len(),
                    from.as_mut_bytes().as_mut_ptr(),
                    &mut from_size,
                    to.as_mut_bytes().as_mut_ptr(),
                    &mut to_size,
                )
            };
            if result.into() {
                if from_size > from_capacity || to_size > to_capacity {
                    return Err(CryptoError::Failed);
                }
                // SAFETY: The provider successfully produced both complete date/time encodings.
                return Ok(unsafe {
                    X509Validity {
                        not_before: X509DateTime::from_provider(from.as_bytes()[..from_size].to_vec()),
                        not_after: X509DateTime::from_provider(to.as_bytes()[..to_size].to_vec()),
                    }
                });
            }
            if from_size <= from_capacity && to_size <= to_capacity {
                break;
            }
            (from_capacity, to_capacity) = (from_size.max(from_capacity), to_size.max(to_capacity));
        }
        Err(CryptoError::Failed)
    }

    pub(super) fn key_usage(&self, certificate: &[u8]) -> Result<usize> {
        let get_key_usage = protocol_fn!(self, x509_get_key_usage);
        let mut usage = 0;
        // SAFETY: `certificate` is valid for the call.
        ensure(unsafe { get_key_usage(certificate.as_ptr(), certificate.len(), &mut usage) })?;
        Ok(usage)
    }

    pub(super) fn extended_key_usage(&self, certificate: &[u8]) -> Result<Vec<u8>> {
        self.certificate_field(protocol_fn!(self, x509_get_extended_key_usage), certificate)
    }

    pub(super) fn basic_constraints(&self, certificate: &[u8]) -> Result<Vec<u8>> {
        self.certificate_field(protocol_fn!(self, x509_get_extended_basic_constraints), certificate)
    }

    pub(super) fn certificate_extension(&self, certificate: &[u8], oid: &[u8]) -> Result<Vec<u8>> {
        let get_extension_data = protocol_fn!(self, x509_get_extension_data);
        // SAFETY: The inputs are valid for the call and `try_output_buffer` passes a buffer writable for `*size`
        // bytes.
        try_output_buffer(X509_BUFFER_SIZE, |buffer, size| unsafe {
            get_extension_data(certificate.as_ptr(), certificate.len(), oid.as_ptr(), oid.len(), buffer, size)
        })
        // Providers report a missing extension by setting the size to zero.
        .map_err(|size| if size == 0 { CryptoError::NotFound } else { CryptoError::Failed })
    }

    pub(super) fn is_public_key_supported(&self, certificate: &[u8]) -> bool {
        let Some(is_supported) = self.protocol_v2().and_then(|v2| v2.x509_is_public_key_supported) else {
            return false;
        };
        // SAFETY: `certificate` is valid for the call.
        unsafe { is_supported(certificate.as_ptr(), certificate.len()) }.into()
    }

    pub(super) fn verify_certificate(&self, certificate: &[u8], ca_certificate: &[u8]) -> Result<()> {
        let verify = protocol_fn!(self, x509_verify_cert);
        // SAFETY: The inputs are valid for the call.
        let result =
            unsafe { verify(certificate.as_ptr(), certificate.len(), ca_certificate.as_ptr(), ca_certificate.len()) };
        ensure_or(result, CryptoError::VerificationFailed)
    }

    pub(super) fn verify_certificate_chain(&self, root_certificate: &[u8], chain: &[u8]) -> Result<()> {
        let verify_chain = protocol_fn!(self, x509_verify_cert_chain);
        // SAFETY: The inputs are valid for the call.
        let result =
            unsafe { verify_chain(root_certificate.as_ptr(), root_certificate.len(), chain.as_ptr(), chain.len()) };
        ensure_or(result, CryptoError::VerificationFailed)
    }

    pub(super) fn certificate_from_chain(&self, chain: &[u8], index: usize) -> Result<Vec<u8>> {
        let get_certificate = protocol_fn!(self, x509_get_cert_from_cert_chain);
        let index = i32::try_from(index).map_err(|_| CryptoError::NotFound)?;
        let mut certificate = core::ptr::null();
        let mut certificate_size = 0;
        // SAFETY: `chain` is valid for the call.
        let result =
            unsafe { get_certificate(chain.as_ptr(), chain.len(), index, &mut certificate, &mut certificate_size) };
        ensure_or(result, CryptoError::NotFound)?;
        // The certificate points into `chain`.
        subslice_of(chain, certificate, certificate_size).map(<[u8]>::to_vec).ok_or(CryptoError::Failed)
    }

    pub(super) fn parse_date_time(&self, date_time: &str) -> Result<X509DateTime> {
        let format_date_time = protocol_fn!(self, x509_format_date_time);
        let date_time = c_string(date_time)?;
        // SAFETY: `date_time` is a NUL-terminated string and `output_buffer` passes an 8-byte aligned buffer
        // writable for `*size` bytes.
        output_buffer(DATE_TIME_SIZE, |buffer, size| unsafe {
            format_date_time(date_time.as_ptr(), buffer.cast(), size)
        })
        // SAFETY: A successful provider call produced the complete date/time encoding.
        .map(|bytes| unsafe { X509DateTime::from_provider(bytes) })
    }

    pub(super) fn compare_date_time(&self, first: &X509DateTime, second: &X509DateTime) -> Result<Ordering> {
        let compare = protocol_fn!(self, x509_compare_date_time);
        let first = aligned_copy(first.as_provider_bytes());
        let second = aligned_copy(second.as_provider_bytes());
        // SAFETY: Both values are 8-byte aligned copies of structures produced by this provider.
        match unsafe { compare(first.as_ptr().cast::<c_void>(), second.as_ptr().cast::<c_void>()) } {
            -1 => Ok(Ordering::Less),
            0 => Ok(Ordering::Equal),
            1 => Ok(Ordering::Greater),
            _ => Err(CryptoError::Failed),
        }
    }

    pub(super) fn asn1_get_tag(&self, data: &[u8], tag: u32) -> Result<(usize, usize)> {
        let get_tag = protocol_fn!(self, asn1_get_tag);
        let range = data.as_ptr_range();
        let mut cursor = range.start.cast_mut();
        let mut length = 0;
        // SAFETY: `cursor` and `end` delimit `data`. `Asn1GetTag` only advances `cursor` and does not write through
        // it.
        ensure_or(unsafe { get_tag(&mut cursor, range.end, &mut length, tag) }, CryptoError::NotFound)?;
        let header = cursor.addr().checked_sub(range.start.addr()).filter(|&header| header <= data.len());
        Ok((header.ok_or(CryptoError::Failed)?, length))
    }
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
mod tests {
    use super::{
        super::{
            protocol::{OneCryptoProtocol, OneCryptoProtocolV2, OneCryptoProtocolV2Extension},
            test_support::*,
        },
        *,
    };
    use crate::service::signature::Signature;

    // Fakes treat the certificate as `[field..]` and return it as the requested field.
    extern "efiapi" fn field(cert: *const u8, len: usize, buffer: *mut u8, size: *mut usize) -> efi::Boolean {
        // SAFETY: `cert` is readable for `len` bytes and the buffer is writable for `*size` bytes.
        unsafe { write_output(input(cert, len), buffer, size) }
    }
    extern "efiapi" fn name(cert: *const u8, len: usize, buffer: *mut u8, size: *mut usize) -> efi::Status {
        // SAFETY: `cert` is readable for `len` bytes and `size` is valid.
        unsafe {
            if len == 0 {
                return efi::Status::NOT_FOUND;
            }
            if buffer.is_null() {
                *size = len + 1;
                return efi::Status::BUFFER_TOO_SMALL;
            }
            core::ptr::copy_nonoverlapping(cert, buffer, len);
            buffer.add(len).write(0);
        }
        efi::Status::SUCCESS
    }
    extern "efiapi" fn number(_cert: *const u8, len: usize, value: *mut usize) -> efi::Boolean {
        // SAFETY: `value` is writable.
        unsafe { value.write(len) };
        boolean(len != 0)
    }
    extern "efiapi" fn tbs_into_cert(cert: *const u8, len: usize, tbs: *mut *mut u8, size: *mut usize) -> efi::Boolean {
        // SAFETY: The outputs are writable.
        unsafe {
            tbs.write(cert.add(1).cast_mut());
            size.write(len - 1);
        }
        boolean(true)
    }
    extern "efiapi" fn tbs_allocated(cert: *const u8, len: usize, tbs: *mut *mut u8, size: *mut usize) -> efi::Boolean {
        // SAFETY: `cert` is readable for `len` bytes and the outputs are writable.
        unsafe {
            tbs.write(pool_buffer(input(cert, len)));
            size.write(len);
        }
        boolean(true)
    }
    extern "efiapi" fn validity(
        cert: *const u8,
        len: usize,
        from: *mut u8,
        from_size: *mut usize,
        to: *mut u8,
        to_size: *mut usize,
    ) -> efi::Boolean {
        // SAFETY: The buffers are writable for their sizes. The fake reports a 72-byte `to` value.
        unsafe {
            let from_ok: bool = write_output(input(cert, len), from, from_size).into();
            let to_ok: bool = write_output(&[0xee; 72], to, to_size).into();
            boolean(from_ok && to_ok)
        }
    }
    extern "efiapi" fn extension(
        cert: *const u8,
        len: usize,
        oid: *const u8,
        oid_len: usize,
        buffer: *mut u8,
        size: *mut usize,
    ) -> efi::Boolean {
        // SAFETY: The inputs are readable and `size` is valid.
        unsafe {
            if input(oid, oid_len) != [1] {
                *size = 0;
                return boolean(false);
            }
            field(cert, len, buffer, size)
        }
    }
    extern "efiapi" fn supported(_cert: *const u8, len: usize) -> efi::Boolean {
        boolean(len != 0)
    }
    extern "efiapi" fn verify(cert: *const u8, len: usize, ca: *const u8, ca_len: usize) -> efi::Boolean {
        // SAFETY: The inputs are readable for their lengths.
        boolean(unsafe { input(cert, len) == input(ca, ca_len) })
    }
    extern "efiapi" fn from_chain(
        chain: *const u8,
        len: usize,
        index: i32,
        cert: *mut *const u8,
        cert_len: *mut usize,
    ) -> efi::Boolean {
        // The fake chain is made of one-byte certificates.
        let Ok(index) = usize::try_from(index) else {
            return boolean(false);
        };
        if index >= len {
            return boolean(false);
        }
        // SAFETY: The outputs are writable and `index` is within the chain.
        unsafe {
            cert.write(chain.add(index));
            cert_len.write(1);
        }
        boolean(true)
    }
    extern "efiapi" fn format_date_time(value: *const u8, date_time: *mut c_void, size: *mut usize) -> efi::Boolean {
        assert!(date_time.cast::<u64>().is_aligned());
        // SAFETY: `value` is NUL-terminated and the buffer is writable for `*size` bytes.
        unsafe { write_output(&[*value], date_time.cast(), size) }
    }
    extern "efiapi" fn compare(first: *const c_void, second: *const c_void) -> i32 {
        assert!(first.cast::<u64>().is_aligned() && second.cast::<u64>().is_aligned());
        // SAFETY: Both values hold at least one byte.
        let (first, second) = unsafe { (*first.cast::<u8>(), *second.cast::<u8>()) };
        if first == b'x' || second == b'x' { -2 } else { first.cmp(&second) as i32 }
    }
    extern "efiapi" fn get_tag(cursor: *mut *mut u8, end: *const u8, length: *mut usize, tag: u32) -> efi::Boolean {
        // SAFETY: `cursor` delimits a readable range with `end`, and the outputs are writable.
        unsafe {
            if (*cursor).cast_const() == end || u32::from(**cursor) != tag {
                return boolean(false);
            }
            *length = usize::from(*(*cursor).add(1));
            *cursor = (*cursor).add(2);
        }
        boolean(true)
    }

    fn x509() -> OneCryptoProtocolV2 {
        let base = OneCryptoProtocol {
            x509_get_subject_name: Some(field),
            x509_get_issuer_name: Some(field),
            x509_get_serial_number: Some(field),
            x509_get_signature_algorithm: Some(field),
            x509_get_extended_key_usage: Some(field),
            x509_get_extended_basic_constraints: Some(field),
            x509_get_common_name: Some(name),
            x509_get_organization_name: Some(name),
            x509_get_version: Some(number),
            x509_get_key_usage: Some(number),
            x509_get_tbs_cert: Some(tbs_into_cert),
            x509_get_validity: Some(validity),
            x509_get_extension_data: Some(extension),
            x509_verify_cert: Some(verify),
            x509_verify_cert_chain: Some(verify),
            x509_get_cert_from_cert_chain: Some(from_chain),
            x509_format_date_time: Some(format_date_time),
            x509_compare_date_time: Some(compare),
            asn1_get_tag: Some(get_tag),
            ..protocol()
        };
        protocol_v2(
            base,
            OneCryptoProtocolV2Extension { x509_is_public_key_supported: Some(supported), ..Default::default() },
        )
    }

    #[test]
    fn test_one_crypto_x509_fields() {
        let crypto = crypto(x509());
        let crypto: &dyn Signature = &crypto;
        let certificate = [7u8; 300];
        for result in [
            crypto.subject_name(&certificate),
            crypto.issuer_name(&certificate),
            crypto.serial_number(&certificate),
            crypto.certificate_signature_algorithm(&certificate),
            crypto.extended_key_usage(&certificate),
            crypto.basic_constraints(&certificate),
            crypto.certificate_extension(&certificate, &[1]),
        ] {
            assert_eq!(result, Ok(certificate.to_vec()));
        }
        assert_eq!(crypto.certificate_extension(&certificate, &[2]), Err(CryptoError::NotFound));
        assert_eq!(crypto.certificate_version(&[0; 3]), Ok(3));
        assert_eq!(crypto.key_usage(&[0; 4]), Ok(4));
        assert_eq!(crypto.key_usage(&[]), Err(CryptoError::Failed));
    }

    #[test]
    fn test_one_crypto_x509_names() {
        let crypto = crypto(x509());
        let crypto: &dyn Signature = &crypto;
        assert_eq!(crypto.common_name(b"Patina"), Ok(String::from("Patina")));
        assert_eq!(crypto.organization_name(b"ODP"), Ok(String::from("ODP")));
        assert_eq!(crypto.common_name(b""), Err(CryptoError::NotFound));
    }

    #[test]
    fn test_one_crypto_x509_tbs_certificate() {
        assert_eq!(Signature::tbs_certificate(&crypto(x509()), &[1, 2, 3]), Ok(vec![2, 3]));
        let protocol = x509();
        let protocol = OneCryptoProtocolV2 {
            base: OneCryptoProtocol { x509_get_tbs_cert: Some(tbs_allocated), ..protocol.base },
            ..protocol
        };
        let crypto = crypto_with_frees(protocol, 1);
        assert_eq!(crypto.tbs_certificate(&[1, 2, 3]), Ok(vec![1, 2, 3]));
    }

    #[test]
    fn test_one_crypto_x509_validity_retries_larger_sizes() {
        let validity = Signature::certificate_validity(&crypto(x509()), &[1, 2]).expect("validity");
        assert_eq!(validity.not_before.as_provider_bytes(), [1, 2]);
        assert_eq!(validity.not_after.as_provider_bytes(), [0xee; 72]);
    }

    #[test]
    fn test_one_crypto_x509_verify() {
        let crypto = crypto(x509());
        let crypto: &dyn Signature = &crypto;
        assert_eq!(crypto.verify_certificate(&[1], &[1]), Ok(()));
        assert_eq!(crypto.verify_certificate(&[1], &[2]), Err(CryptoError::VerificationFailed));
        assert_eq!(crypto.verify_certificate_chain(&[1], &[1]), Ok(()));
        assert_eq!(crypto.verify_certificate_chain(&[1], &[2]), Err(CryptoError::VerificationFailed));
        assert!(crypto.is_public_key_supported(&[1]));
        assert!(!crypto.is_public_key_supported(&[]));
        assert!(!super::super::test_support::crypto(protocol()).is_public_key_supported(&[1]));
        let v1 = super::super::test_support::crypto(OneCryptoProtocol { major: 1, ..x509().base });
        assert!(!v1.is_public_key_supported(&[1]));
    }

    #[test]
    fn test_one_crypto_x509_certificate_from_chain() {
        let crypto = crypto(x509());
        let crypto: &dyn Signature = &crypto;
        assert_eq!(crypto.certificate_from_chain(&[4, 5, 6], 1), Ok(vec![5]));
        assert_eq!(crypto.certificate_from_chain(&[4, 5, 6], 3), Err(CryptoError::NotFound));
        assert_eq!(crypto.certificate_from_chain(&[4], usize::MAX), Err(CryptoError::NotFound));
    }

    #[test]
    fn test_one_crypto_x509_date_time() {
        let crypto = crypto(x509());
        let crypto: &dyn Signature = &crypto;
        let early = crypto.parse_date_time("20240101000000Z").expect("format");
        let late = crypto.parse_date_time("30240101000000Z").expect("format");
        assert_eq!(crypto.compare_date_time(&early, &late), Ok(Ordering::Less));
        assert_eq!(crypto.compare_date_time(&late, &early), Ok(Ordering::Greater));
        assert_eq!(crypto.compare_date_time(&early, &early), Ok(Ordering::Equal));
        let invalid = crypto.parse_date_time("x").expect("format");
        assert_eq!(crypto.compare_date_time(&invalid, &early), Err(CryptoError::Failed));
        assert_eq!(crypto.parse_date_time("\0"), Err(CryptoError::InvalidParameter));
    }

    #[test]
    fn test_one_crypto_x509_asn1_get_tag() {
        let crypto = crypto(x509());
        let crypto: &dyn Signature = &crypto;
        assert_eq!(crypto.asn1_get_tag(&[0x30, 5, 0, 0, 0, 0, 0], 0x30), Ok((2, 5)));
        assert_eq!(crypto.asn1_get_tag(&[0x30, 5], 0x02), Err(CryptoError::NotFound));
        assert_eq!(crypto.asn1_get_tag(&[], 0x30), Err(CryptoError::NotFound));
    }
}
