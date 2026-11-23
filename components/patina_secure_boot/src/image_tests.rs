//! Authenticode input tests.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use super::*;
use crate::test_support::*;
use alloc::{boxed::Box, rc::Rc, vec};
use core::cell::RefCell;
use patina::crypto::hash::{MockDigestContext, MockHash};

#[test]
fn test_secure_boot_image_ranges_and_certificates() {
    let bytes = pe(true);
    let image = AuthenticodeImage::parse(&bytes).unwrap();
    assert_eq!(image.ranges, vec![0..0xd8, 0xdc..0x128, 0x130..0x200, 0x200..0x400, 0x400..0x400]);
    assert_eq!(image.signatures().collect::<Vec<_>>(), vec![&[1, 2, 3][..]]);
    let unsigned = pe(false);
    assert_eq!(AuthenticodeImage::parse(&unsigned).unwrap().signatures().count(), 0);
}

#[test]
fn test_secure_boot_image_hash_streams_and_caches() {
    let bytes = pe(true);
    let mut image = AuthenticodeImage::parse(&bytes).unwrap();
    let expected = [&bytes[..0xd8], &bytes[0xdc..0x128], &bytes[0x130..0x400]].concat();
    let observed = Rc::new(RefCell::new(Vec::new()));
    let output = observed.clone();
    let mut hash = MockHash::new();
    hash.expect_new_hash().once().returning_st(move |_| {
        let mut context = MockDigestContext::new();
        let output = output.clone();
        context.expect_update().returning_st(move |bytes| {
            output.borrow_mut().extend_from_slice(bytes);
            Ok(())
        });
        context.expect_finalize().once().returning(|| Ok(vec![0xaa; 32]));
        Ok(Box::new(context))
    });
    for _ in 0..2 {
        assert_eq!(image.digest(&hash, HashAlgorithm::Sha256).unwrap(), &[0xaa; 32]);
    }
    assert_eq!(*observed.borrow(), expected);
}

#[test]
fn test_secure_boot_image_rejects_truncation_and_bad_layouts() {
    let bytes = pe(true);
    for length in 0..bytes.len() {
        assert!(AuthenticodeImage::parse(&bytes[..length]).is_err(), "length {length}");
    }
    for (offset, value) in [
        (0xd4, 0x100u32),
        (0xd4, u32::MAX),
        (0x128, 0x3ff),
        (0x128, 0x408),
        (0x12c, u32::MAX),
        (0x198, u32::MAX),
        (0x19c, 0),
        (0x19c, 0x300),
    ] {
        let mut bytes = pe(true);
        bytes[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
        assert!(AuthenticodeImage::parse(&bytes).is_err(), "offset {offset:x}, value {value:x}");
    }
}

#[test]
fn test_secure_boot_image_malformed_certificate_stops_iteration() {
    for length in [0u32, 7, 17, u32::MAX] {
        let mut bytes = pe(true);
        bytes[0x400..0x404].copy_from_slice(&length.to_le_bytes());
        let image = AuthenticodeImage::parse(&bytes).unwrap();
        let mut signatures = image.signatures();
        assert!(signatures.next().is_none());
        assert!(signatures.next().is_none());
    }
    for (offset, value) in [(0x404, 0x100u16), (0x406, 0xffff)] {
        let mut bytes = pe(true);
        bytes[offset..offset + 2].copy_from_slice(&value.to_le_bytes());
        assert_eq!(AuthenticodeImage::parse(&bytes).unwrap().signatures().count(), 0);
    }
}

#[test]
fn test_secure_boot_image_hash_failure_is_propagated() {
    let bytes = pe(false);
    let mut image = AuthenticodeImage::parse(&bytes).unwrap();
    let mut hash = MockHash::new();
    hash.expect_new_hash().returning(|_| Err(CryptoError::Unsupported));
    assert_eq!(image.digest(&hash, HashAlgorithm::Sha256), Err(CryptoError::Unsupported));
}

#[test]
fn test_secure_boot_image_pe32_without_security_directory() {
    let mut bytes = pe(false);
    bytes[0x94..0x96].copy_from_slice(&0xe0u16.to_le_bytes());
    bytes[0x98..0x9a].copy_from_slice(&0x10bu16.to_le_bytes());
    bytes[0xf4..0xf8].copy_from_slice(&0u32.to_le_bytes());
    bytes.copy_within(0x188..0x1b0, 0x178);
    let image = AuthenticodeImage::parse(&bytes).unwrap();
    assert_eq!(image.ranges, vec![0..0xd8, 0xdc..0x200, 0x200..0x400, 0x400..0x400]);
    assert_eq!(image.signatures().count(), 0);
}

#[test]
fn test_secure_boot_image_guid_and_multiple_signatures() {
    let mut bytes = pe(true);
    bytes[0x400..0x404].copy_from_slice(&32u32.to_le_bytes());
    bytes[0x406..0x408].copy_from_slice(&0x0ef1u16.to_le_bytes());
    bytes.truncate(0x408);
    bytes.extend_from_slice(BinaryGuid::from_string("4aafd29d-68df-49ee-8aa9-347d375665a7").as_bytes());
    bytes.extend_from_slice(&[4, 5, 6, 0, 0, 0, 0, 0]);
    let record = bytes[0x400..].to_vec();
    bytes.extend_from_slice(&record);
    bytes[0x12c..0x130].copy_from_slice(&64u32.to_le_bytes());
    let image = AuthenticodeImage::parse(&bytes).unwrap();
    assert_eq!(image.signatures().collect::<Vec<_>>(), vec![&[4, 5, 6, 0, 0, 0, 0, 0][..]; 2]);
}
