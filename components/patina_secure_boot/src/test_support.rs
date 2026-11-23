//! Synthetic PE images and signature lists used by the unit tests.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use alloc::{boxed::Box, vec, vec::Vec};
use patina::{
    BinaryGuid,
    crypto::hash::{HashAlgorithm, MockDigestContext, MockHash},
};

pub(crate) const SHA256: &str = "c1c41626-504c-4092-aca9-41f936934328";
pub(crate) const X509: &str = "a5c059a1-94e4-4aa7-87b5-ab155c2bf072";
pub(crate) const TBS256: &str = "3bd2a492-96c0-4079-b420-fcf98ef103ed";

pub(crate) fn list(guid: &str, data: &[u8], v2: bool) -> Vec<u8> {
    let stride = data.len() + if v2 { 0 } else { 16 };
    let mut list = Vec::new();
    list.extend_from_slice(BinaryGuid::from_string(guid).as_bytes());
    list.extend_from_slice(&((28 + stride) as u32).to_le_bytes());
    list.extend_from_slice(&0u32.to_le_bytes());
    list.extend_from_slice(&(stride as u32).to_le_bytes());
    if !v2 {
        list.extend_from_slice(&[0x55; 16]);
    }
    list.extend_from_slice(data);
    list
}

pub(crate) fn pe(signed: bool) -> Vec<u8> {
    let mut bytes = vec![0; 0x400];
    bytes[..2].copy_from_slice(b"MZ");
    bytes[0x3c..0x40].copy_from_slice(&0x80u32.to_le_bytes());
    bytes[0x80..0x84].copy_from_slice(b"PE\0\0");
    bytes[0x84..0x86].copy_from_slice(&0x8664u16.to_le_bytes());
    bytes[0x86..0x88].copy_from_slice(&1u16.to_le_bytes());
    bytes[0x94..0x96].copy_from_slice(&240u16.to_le_bytes());
    bytes[0x98..0x9a].copy_from_slice(&0x20bu16.to_le_bytes());
    bytes[0xb8..0xbc].copy_from_slice(&0x1000u32.to_le_bytes());
    bytes[0xbc..0xc0].copy_from_slice(&0x200u32.to_le_bytes());
    bytes[0xd0..0xd4].copy_from_slice(&0x2000u32.to_le_bytes());
    bytes[0xd4..0xd8].copy_from_slice(&0x200u32.to_le_bytes());
    bytes[0x104..0x108].copy_from_slice(&16u32.to_le_bytes());
    bytes[0x188..0x18d].copy_from_slice(b".text");
    bytes[0x190..0x194].copy_from_slice(&0x200u32.to_le_bytes());
    bytes[0x194..0x198].copy_from_slice(&0x1000u32.to_le_bytes());
    bytes[0x198..0x19c].copy_from_slice(&0x200u32.to_le_bytes());
    bytes[0x19c..0x1a0].copy_from_slice(&0x200u32.to_le_bytes());
    bytes[0x200..].fill(0xa5);
    if signed {
        bytes[0x128..0x12c].copy_from_slice(&0x400u32.to_le_bytes());
        bytes[0x12c..0x130].copy_from_slice(&16u32.to_le_bytes());
        bytes.extend_from_slice(&11u32.to_le_bytes());
        bytes.extend_from_slice(&0x200u16.to_le_bytes());
        bytes.extend_from_slice(&2u16.to_le_bytes());
        bytes.extend_from_slice(&[1, 2, 3, 0, 0, 0, 0, 0]);
    }
    bytes
}

pub(crate) fn hash() -> MockHash {
    let mut hash = MockHash::new();
    hash.expect_new_hash().withf(|algorithm| *algorithm == HashAlgorithm::Sha256).returning(|_| {
        let mut context = MockDigestContext::new();
        context.expect_update().returning(|_| Ok(()));
        context.expect_finalize().returning(|| Ok(vec![0xaa; 32]));
        Ok(Box::new(context))
    });
    hash
}
