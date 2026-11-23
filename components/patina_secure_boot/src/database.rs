//! Borrowed, alignment-independent parsing of UEFI signature databases.
//!
//! Iterators report malformed input rather than silently truncating it. Consumers may
//! use the valid prefix of an allow-list, but must reject an incomplete revoke-list.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use core::{fmt, iter::FusedIterator};
use patina::{BinaryGuid, crypto::hash::HashAlgorithm};
use zerocopy::{
    FromBytes,
    byteorder::{LittleEndian, U32},
};
use zerocopy_derive::{Immutable, IntoBytes, KnownLayout, Unaligned};

/// Wire layout of `EFI_SIGNATURE_LIST`. All lengths are little-endian byte counts.
#[repr(C)]
#[derive(Debug, FromBytes, IntoBytes, KnownLayout, Immutable, Unaligned)]
pub struct SignatureListHeader {
    /// GUID identifying the entry encoding.
    pub signature_type: [u8; 16],
    /// Total list length, including this fixed header.
    pub list_size: U32<LittleEndian>,
    /// Length of the type-specific header after this fixed header.
    pub header_size: U32<LittleEndian>,
    /// Length of each signature entry, including any owner GUID.
    pub signature_size: U32<LittleEndian>,
}

/// Wire layout of a legacy `EFI_SIGNATURE_DATA` entry.
#[repr(C)]
#[derive(FromBytes, IntoBytes, KnownLayout, Immutable, Unaligned)]
pub struct SignatureData {
    /// Agent that enrolled this signature.
    pub owner: [u8; 16],
    /// Type-specific signature bytes.
    pub data: [u8],
}

/// Wire layout of `EFI_SIGNATURE_V2_DATA`, which has no owner GUID.
#[repr(C)]
#[derive(FromBytes, IntoBytes, KnownLayout, Immutable, Unaligned)]
pub struct SignatureV2Data {
    /// Type-specific signature bytes.
    pub data: [u8],
}

/// Legacy certificate-hash payload, including the 16-byte UEFI revocation time.
///
/// V2 certificate-hash entries contain only the digest, without a time field.
#[repr(C)]
#[derive(FromBytes, IntoBytes, KnownLayout, Immutable, Unaligned)]
pub struct CertificateHash<const N: usize> {
    /// Digest of the DER-encoded TBSCertificate.
    pub digest: [u8; N],
    /// Packed `EFI_TIME` value.
    pub revocation_time: [u8; 16],
}

/// Structural failure while parsing a signature database.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DatabaseError {
    /// Fixed header, type-specific header, or list extends past the input.
    Truncated,
    /// A size is zero or smaller than the structure it describes.
    InvalidSize,
    /// An entry has a partial trailing payload.
    PartialEntry,
    /// A recognized signature type has an unexpected payload length or header.
    InvalidPayload,
}

impl fmt::Display for DatabaseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Truncated => "truncated signature database",
            Self::InvalidSize => "invalid signature database size",
            Self::PartialEntry => "partial signature database entry",
            Self::InvalidPayload => "invalid signature database payload",
        })
    }
}

impl core::error::Error for DatabaseError {}

/// Meaning of a supported signature-list type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SignatureKind {
    /// Authenticode digest of an image.
    ImageHash(HashAlgorithm),
    /// Complete DER-encoded X.509 certificate.
    Certificate,
    /// Digest of a certificate's TBSCertificate.
    CertificateHash(HashAlgorithm),
    /// A type not interpreted by this implementation.
    Unknown,
}

/// Recognized signature-list encoding.
#[derive(Debug, Clone, Copy)]
pub struct SignatureFormat {
    /// Semantic type of each entry.
    pub kind: SignatureKind,
    /// Whether entries use the ownerless V2 layout.
    pub v2: bool,
}

impl SignatureFormat {
    /// Classifies a signature type GUID in UEFI binary byte order.
    pub fn from_guid(guid: &[u8; 16]) -> Self {
        let guid = BinaryGuid::from_bytes(guid);
        for (text, kind, v2) in [
            ("c1c41626-504c-4092-aca9-41f936934328", SignatureKind::ImageHash(HashAlgorithm::Sha256), false),
            ("ff3e5307-9fd0-48c9-85f1-8ad56c701e01", SignatureKind::ImageHash(HashAlgorithm::Sha384), false),
            ("093e0fae-a6c4-4f50-9f1b-d41e2b89c19a", SignatureKind::ImageHash(HashAlgorithm::Sha512), false),
            ("a5c059a1-94e4-4aa7-87b5-ab155c2bf072", SignatureKind::Certificate, false),
            ("3bd2a492-96c0-4079-b420-fcf98ef103ed", SignatureKind::CertificateHash(HashAlgorithm::Sha256), false),
            ("7076876e-80c2-4ee6-aad2-28b349a6865b", SignatureKind::CertificateHash(HashAlgorithm::Sha384), false),
            ("446dbf63-2502-4cda-bcfa-2465d2b0fe9d", SignatureKind::CertificateHash(HashAlgorithm::Sha512), false),
            ("65325437-ca92-441e-943d-4e003faeda97", SignatureKind::ImageHash(HashAlgorithm::Sha256), true),
            ("45db3553-f9a6-4026-8e48-eb1e4b07185c", SignatureKind::ImageHash(HashAlgorithm::Sha384), true),
            ("d2291d97-f066-4abf-9c57-6363e5fd6903", SignatureKind::ImageHash(HashAlgorithm::Sha512), true),
            ("79518039-4715-4393-bdf8-d8e3c67fbac7", SignatureKind::Certificate, true),
            ("af4d21cd-7627-4b81-9e96-d4f3bbc3fae9", SignatureKind::CertificateHash(HashAlgorithm::Sha256), true),
            ("78860e15-f2eb-4d16-8156-231518fb7688", SignatureKind::CertificateHash(HashAlgorithm::Sha384), true),
            ("4d46147a-fa79-43a9-8836-00341c708a70", SignatureKind::CertificateHash(HashAlgorithm::Sha512), true),
        ] {
            if guid == BinaryGuid::from_string(text) {
                return Self { kind, v2 };
            }
        }
        Self { kind: SignatureKind::Unknown, v2: false }
    }
}

/// A checked list envelope borrowing its headers and entries from the database.
pub struct SignatureList<'a> {
    /// Fixed list header.
    pub header: &'a SignatureListHeader,
    /// Type-specific header.
    pub type_header: &'a [u8],
    data: &'a [u8],
}

impl<'a> SignatureList<'a> {
    /// Returns entries, including a final error if the list has a partial trailing entry.
    pub fn entries(&self) -> impl Iterator<Item = Result<SignatureEntry<'a>, DatabaseError>> + '_ {
        let format = SignatureFormat::from_guid(&self.header.signature_type);
        self.data.chunks(self.header.signature_size.get() as usize).map(move |bytes| {
            if bytes.len() != self.header.signature_size.get() as usize {
                return Err(DatabaseError::PartialEntry);
            }
            if !self.type_header.is_empty() && format.kind != SignatureKind::Unknown {
                return Err(DatabaseError::InvalidPayload);
            }
            let (owner, data) = if format.v2 || format.kind == SignatureKind::Unknown {
                (None, bytes)
            } else {
                let (owner, data) = bytes.split_first_chunk::<16>().ok_or(DatabaseError::InvalidSize)?;
                (Some(owner), data)
            };
            let expected = match format.kind {
                SignatureKind::ImageHash(algorithm) => Some(algorithm.digest_size()),
                SignatureKind::CertificateHash(algorithm) => {
                    Some(algorithm.digest_size() + if format.v2 { 0 } else { 16 })
                }
                SignatureKind::Certificate if data.is_empty() => return Err(DatabaseError::InvalidPayload),
                _ => None,
            };
            if expected.is_some_and(|size| size != data.len()) {
                return Err(DatabaseError::InvalidPayload);
            }
            Ok(SignatureEntry { format, owner, data })
        })
    }
}

/// One parsed signature entry.
pub struct SignatureEntry<'a> {
    /// Signature semantics and encoding.
    pub format: SignatureFormat,
    /// Legacy owner GUID, absent in V2 entries.
    pub owner: Option<&'a [u8; 16]>,
    /// Payload, excluding the legacy owner GUID.
    pub data: &'a [u8],
}

impl SignatureEntry<'_> {
    /// Returns the certificate digest without the legacy revocation-time suffix.
    pub fn certificate_digest(&self) -> Option<&[u8]> {
        match self.format.kind {
            SignatureKind::CertificateHash(algorithm) => self.data.get(..algorithm.digest_size()),
            _ => None,
        }
    }
}

/// Fused iterator over signature-list envelopes. A structural failure ends iteration.
pub struct SignatureDatabase<'a> {
    remaining: &'a [u8],
}

impl<'a> SignatureDatabase<'a> {
    /// Borrows a database without allocating or assuming alignment.
    pub const fn new(bytes: &'a [u8]) -> Self {
        Self { remaining: bytes }
    }
}

impl<'a> Iterator for SignatureDatabase<'a> {
    type Item = Result<SignatureList<'a>, DatabaseError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining.is_empty() {
            return None;
        }
        let bytes = core::mem::take(&mut self.remaining);
        Some((|| {
            let (header, _) = SignatureListHeader::ref_from_prefix(bytes).map_err(|_| DatabaseError::Truncated)?;
            let list_size = header.list_size.get() as usize;
            if list_size < size_of::<SignatureListHeader>() || header.signature_size.get() == 0 {
                return Err(DatabaseError::InvalidSize);
            }
            let list = bytes.get(..list_size).ok_or(DatabaseError::Truncated)?;
            let payload = &list[size_of::<SignatureListHeader>()..];
            let header_size = header.header_size.get() as usize;
            let type_header = payload.get(..header_size).ok_or(DatabaseError::Truncated)?;
            self.remaining = &bytes[list_size..];
            Ok(SignatureList { header, type_header, data: &payload[header_size..] })
        })())
    }
}

impl FusedIterator for SignatureDatabase<'_> {}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
mod tests {
    use super::*;
    use crate::test_support::*;
    use alloc::vec;
    use zerocopy::IntoBytes;

    #[test]
    fn test_secure_boot_database_wire_layouts() {
        assert_eq!(size_of::<SignatureListHeader>(), 28);
        assert_eq!(align_of::<SignatureListHeader>(), 1);
        assert_eq!(size_of::<CertificateHash<32>>(), 48);
        let bytes = [0u8; 48];
        let legacy = SignatureData::ref_from_bytes(&bytes).unwrap();
        assert_eq!(legacy.data.len(), 32);
        let v2 = SignatureV2Data::ref_from_bytes(&bytes).unwrap();
        assert_eq!(v2.data.len(), 48);
    }

    #[test]
    fn test_secure_boot_database_unaligned_and_multiple_lists() {
        let mut bytes = vec![0xff];
        bytes.extend(list(SHA256, &[0xaa; 32], false));
        bytes.extend(list(X509, &[1, 2, 3], false));
        let lists: alloc::vec::Vec<_> = SignatureDatabase::new(&bytes[1..]).map(Result::unwrap).collect();
        assert_eq!(lists.len(), 2);
        let entry = lists[0].entries().next().unwrap().unwrap();
        assert_eq!(entry.owner, Some(&[0x55; 16]));
        assert_eq!(entry.data, &[0xaa; 32]);
        assert_eq!(lists[0].header.as_bytes().len(), 28);
    }

    #[test]
    fn test_secure_boot_database_v2_short_certificate() {
        let bytes = list("79518039-4715-4393-bdf8-d8e3c67fbac7", &[1, 2], true);
        let list = SignatureDatabase::new(&bytes).next().unwrap().unwrap();
        let entry = list.entries().next().unwrap().unwrap();
        assert_eq!(entry.owner, None);
        assert_eq!(entry.data, &[1, 2]);
    }

    #[test]
    fn test_secure_boot_database_truncation_and_invalid_sizes() {
        let valid = list(SHA256, &[0xaa; 32], false);
        for size in 1..valid.len() {
            let mut iterator = SignatureDatabase::new(&valid[..size]);
            assert!(iterator.next().unwrap().is_err(), "length {size}");
            assert!(iterator.next().is_none());
            assert!(iterator.next().is_none());
        }
        for (offset, value) in [(16, 0u32), (16, 27), (16, u32::MAX), (20, u32::MAX), (24, 0)] {
            let mut bytes = valid.clone();
            bytes[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
            assert!(SignatureDatabase::new(&bytes).next().unwrap().is_err());
        }
        assert!(SignatureDatabase::new(&[]).next().is_none());
    }

    #[test]
    fn test_secure_boot_database_preserves_prefix_and_reports_partial_entry() {
        let mut bytes = list(SHA256, &[0xaa; 32], false);
        bytes.push(0);
        let size = bytes.len() as u32;
        bytes[16..20].copy_from_slice(&size.to_le_bytes());
        let list = SignatureDatabase::new(&bytes).next().unwrap().unwrap();
        let mut entries = list.entries();
        assert!(entries.next().unwrap().is_ok());
        assert!(matches!(entries.next(), Some(Err(DatabaseError::PartialEntry))));
    }

    #[test]
    fn test_secure_boot_database_payload_validation() {
        for (guid, data, v2) in [
            (SHA256, &[][..], false),
            (SHA256, &[0; 31][..], false),
            (X509, &[][..], false),
            ("65325437-ca92-441e-943d-4e003faeda97", &[0; 31][..], true),
        ] {
            let bytes = list(guid, data, v2);
            let parsed = SignatureDatabase::new(&bytes).next().unwrap().unwrap();
            assert!(parsed.entries().next().unwrap().is_err());
        }
        let bytes = list(TBS256, &[0; 48], false);
        let parsed = SignatureDatabase::new(&bytes).next().unwrap().unwrap();
        let entry = parsed.entries().next().unwrap().unwrap();
        assert_eq!(entry.certificate_digest(), Some(&[0; 32][..]));
        assert!(SignatureFormat::from_guid(&[0; 16]).kind == SignatureKind::Unknown);
    }
}
