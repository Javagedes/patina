//! ACPI Table Definitions.
//!
//! Defines standard formats for system ACPI tables.
//! Supports only ACPI version >= 2.0.
//! Fields corresponding to ACPI 1.0 are preceded with an underscore (`_`) and are not in use.
//!
//! ## License
//!
//! Copyright (C) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0

use crate::error::AcpiError;
use alloc::{boxed::Box, vec::Vec};
use zerocopy::little_endian::U64;

use core::{fmt::Debug, mem, ptr};

use zerocopy_derive::*;

/// Represents the FADT for ACPI 2.0+.
/// Equivalent to EFI_ACPI_3_0_FIXED_ACPI_DESCRIPTION_TABLE.
#[repr(C, packed)]
#[derive(Default, FromBytes, IntoBytes, Unaligned, KnownLayout, Immutable)]
pub(crate) struct AcpiFadt {
    // Standard ACPI header.
    pub(crate) header: AcpiTableHeader,
    // Inner FADT data.
    pub(crate) inner: FadtData,
}

impl Clone for AcpiFadt {
    fn clone(&self) -> Self {
        Self { header: self.header().clone(), inner: self.inner().clone() }
    }
}

impl Debug for AcpiFadt {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("AcpiFadt").field("header", &self.header()).field("inner", &self.inner()).finish()
    }
}

/// Reads unaligned fields on the FADT.
/// Fields on the FADT may be unaligned, since by specification the FADT is packed.
impl AcpiFadt {
    pub fn header(&self) -> AcpiTableHeader {
        // SAFETY: `self.header` is always a valid, initialized ACPI header.
        unsafe { ptr::read_unaligned(ptr::addr_of!(self.header)) }
    }

    pub fn inner(&self) -> FadtData {
        // SAFETY: `self.inner` is always a valid, initialized FADT data structure.
        unsafe { ptr::read_unaligned(ptr::addr_of!(self.inner)) }
    }

    pub(crate) fn x_firmware_ctrl(&self) -> u64 {
        self.inner.x_firmware_ctrl
    }

    pub(crate) fn x_dsdt(&self) -> u64 {
        self.inner.x_dsdt
    }

    pub(crate) fn set_x_firmware_ctrl(&mut self, address: u64) {
        self.inner.x_firmware_ctrl = address;
    }

    pub(crate) fn set_x_dsdt(&mut self, address: u64) {
        self.inner.x_dsdt = address;
    }
}

#[repr(C, packed)]
#[derive(Default, Clone, Debug, FromBytes, IntoBytes, Unaligned, KnownLayout, Immutable)]
pub(crate) struct FadtData {
    pub(crate) _firmware_ctrl: u32,
    pub(crate) _dsdt: u32,
    pub(crate) _reserved0: u8,

    pub(crate) preferred_pm_profile: u8,
    pub(crate) sci_int: u16,
    pub(crate) smi_cmd: u32,
    pub(crate) acpi_enable: u8,
    pub(crate) acpi_disable: u8,
    pub(crate) s4bios_req: u8,
    pub(crate) pstate_cnt: u8,
    pub(crate) pm1a_evt_blk: u32,
    pub(crate) pm1b_evt_blk: u32,
    pub(crate) pm1a_cnt_blk: u32,
    pub(crate) pm1b_cnt_blk: u32,
    pub(crate) pm2_cnt_blk: u32,
    pub(crate) pm_tmr_blk: u32,
    pub(crate) gpe0_blk: u32,
    pub(crate) gpe1_blk: u32,
    pub(crate) pm1_evt_len: u8,
    pub(crate) pm1_cnt_len: u8,
    pub(crate) pm2_cnt_len: u8,
    pub(crate) pm_tmr_len: u8,
    pub(crate) gpe0_blk_len: u8,
    pub(crate) gpe1_blk_len: u8,
    pub(crate) gpe1_base: u8,
    pub(crate) cst_cnt: u8,
    pub(crate) p_lvl2_lat: u16,
    pub(crate) p_lvl3_lat: u16,
    pub(crate) flush_size: u16,
    pub(crate) flush_stride: u16,
    pub(crate) duty_offset: u8,
    pub(crate) duty_width: u8,
    pub(crate) day_alrm: u8,
    pub(crate) mon_alrm: u8,
    pub(crate) century: u8,
    pub(crate) ia_pc_boot_arch: u16,
    pub(crate) reserved1: u8,
    pub(crate) flags: u32,
    pub(crate) reset_reg: GenericAddressStructure,
    pub(crate) reset_value: u8,
    pub(crate) reserved2: [u8; 3],

    /// Addresses of the FACS and DSDT (64-bit)
    pub(crate) x_firmware_ctrl: u64,
    pub(crate) x_dsdt: u64,

    pub(crate) x_pm1a_evt_blk: GenericAddressStructure,
    pub(crate) x_pm1b_evt_blk: GenericAddressStructure,
    pub(crate) x_pm1a_cnt_blk: GenericAddressStructure,
    pub(crate) x_pm1b_cnt_blk: GenericAddressStructure,
    pub(crate) x_pm2_cnt_blk: GenericAddressStructure,
    pub(crate) x_pm_tmr_blk: GenericAddressStructure,
    pub(crate) x_gpe0_blk: GenericAddressStructure,
    pub(crate) x_gpe1_blk: GenericAddressStructure,
}

/// Represents an ACPI address space for ACPI 2.0+.
/// Equivalent to EFI_ACPI_3_0_GENERIC_ADDRESS_STRUCTURE.
#[repr(C, packed)]
#[derive(Debug, Clone, Default, Copy, FromBytes, IntoBytes, Unaligned, KnownLayout, Immutable)]
pub struct GenericAddressStructure {
    address_space_id: u8,
    register_bit_width: u8,
    register_bit_offset: u8,
    access_size: u8,
    address: u64,
}

/// Represents the FACS for ACPI 2.0+.
/// Note that the FACS does not have a standard ACPI header.
/// The FACS is not present in the list of installed ACPI tables; instead, it is only accessible through the FADT's `x_firmware_ctrl` field.
/// The FACS is always allocated in NVS, and is required to be 64B-aligned.
/// Equivalent to EFI_ACPI_3_0_FIRMWARE_ACPI_CONTROL_STRUCTURE.
#[repr(C, packed)]
#[derive(Default, Clone, FromBytes, IntoBytes, Unaligned, KnownLayout, Immutable)]
pub struct AcpiFacs {
    pub(crate) signature: u32,
    pub(crate) length: u32,
    pub(crate) hardware_signature: u32,

    pub(crate) _firmware_waking_vector: u32,

    pub(crate) global_lock: u32,
    pub(crate) flags: u32,
    pub(crate) x_firmware_waking_vector: u64,
    pub(crate) version: u8,
    pub(crate) reserved: [u8; 31],
}

/// Represents the DSDT for ACPI 2.0+.
/// The DSDT is not present in the list of installed ACPI tables; instead, it is only accessible through the FADT's `x_dsdt` field.
/// The DSDT has a standard header followed by variable-length AML bytecode.
/// The `length` field of the header tells us the number of trailing bytes representing bytecode.
#[repr(C, packed)]
#[derive(Default, FromBytes, IntoBytes, Unaligned, KnownLayout, Immutable)]
pub struct AcpiDsdt {
    pub(crate) header: AcpiTableHeader,
}

/// Represents the RSDP for ACPI 2.0+.
/// The RSDP is not a standard ACPI table and does not have a standard header.
/// It is not present in the list of installed tables and is not directly accessible.
/// Equivalent to EFI_ACPI_3_0_ROOT_SYSTEM_DESCRIPTION_POINTER.
#[repr(C, packed)]
#[derive(Default, Debug, FromBytes, IntoBytes, Unaligned, KnownLayout, Immutable)]
pub struct AcpiRsdp {
    pub(crate) signature: u64,

    pub(crate) checksum: u8,

    pub(crate) oem_id: [u8; 6],
    pub(crate) revision: u8,

    pub(crate) _rsdt_address: u32,

    pub(crate) length: u32,
    pub(crate) xsdt_address: u64,
    pub(crate) extended_checksum: u8,
    pub(crate) reserved: [u8; 3],
}

/// Represents the XSDT for ACPI 2.0+.
/// The XSDT has a standard header followed by 64-bit addresses of installed tables.
/// The `length` field of the header tells us the number of trailing bytes representing table entries.
#[repr(C, packed)]
#[derive(FromBytes, IntoBytes, Unaligned, KnownLayout, Immutable)]
pub struct AcpiXsdt {
    pub(crate) header: AcpiTableHeader,
    pub(crate) entries: [U64],
}

impl Debug for AcpiXsdt {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("AcpiXsdt").field("header", &self.header).field("entries", &self.entries.iter().len()).finish()
    }
}

/// Stores implementation-specific data about the XSDT.
pub(crate) struct AcpiXsdtMetadata {
    pub(crate) n_entries: usize,
    pub(crate) max_capacity: usize,
    pub(crate) slice: Box<[u8], &'static dyn alloc::alloc::Allocator>,
}

impl AcpiXsdtMetadata {
    // Get the 4-byte length (bytes 4..8 of the header).
    pub(crate) fn get_length(&self) -> Result<u32, AcpiError> {
        // XSDT always starts with header.
        let length_offset = mem::offset_of!(AcpiTableHeader, length);
        // Grab the current length from the correct offset in the header.
        self.slice
            .get(length_offset..length_offset + mem::size_of::<u32>()) // Length is a u32
            .and_then(|b| b.try_into().ok())
            .map(u32::from_le_bytes)
            .ok_or(AcpiError::XsdtOverflow)
    }

    // Set the 4-byte length (bytes 4..8 of the header).
    pub(crate) fn set_length(&mut self, new_len: u32) {
        // XSDT always starts with header.
        let length_offset = mem::offset_of!(AcpiTableHeader, length);
        // Write the new length into the correct offset in the header.
        self.slice[length_offset..length_offset + mem::size_of::<u32>()] // Length is a u32
            .copy_from_slice(&new_len.to_le_bytes());
    }

    /// Set the 6-byte OEM ID (bytes 10..16 of the header).
    pub(crate) fn set_oem_id(&mut self, new_id: [u8; 6]) {
        let offset = mem::offset_of!(AcpiTableHeader, oem_id);
        let end = offset + mem::size_of::<[u8; 6]>();
        self.slice[offset..end].copy_from_slice(&new_id);
    }

    /// Set the 8-byte OEM Table ID (bytes 16..24 of the header).
    pub(crate) fn set_oem_table_id(&mut self, new_table_id: [u8; 8]) {
        let offset = mem::offset_of!(AcpiTableHeader, oem_table_id);
        let end = offset + mem::size_of::<[u8; 8]>();
        self.slice[offset..end].copy_from_slice(&new_table_id);
    }

    /// Set the 4-byte OEM Revision (bytes 24..28 of the header).
    pub(crate) fn set_oem_revision(&mut self, new_rev: u32) {
        let offset = mem::offset_of!(AcpiTableHeader, oem_revision);
        let end = offset + mem::size_of::<u32>();
        self.slice[offset..end].copy_from_slice(&new_rev.to_le_bytes());
    }
}

/// Represents a standard ACPI header.
/// Equivalent to EFI_ACPI_DESCRIPTION_HEADER.
#[repr(C, packed)]
#[derive(Default, Clone, Debug, FromBytes, IntoBytes, Unaligned, KnownLayout, Immutable)]
pub struct AcpiTableHeader {
    pub signature: u32,
    pub length: u32,
    pub revision: u8,
    pub checksum: u8,
    pub oem_id: [u8; 6],
    pub oem_table_id: [u8; 8],
    pub oem_revision: u32,
    pub creator_id: u32,
    pub creator_revision: u32,
}

impl AcpiTableHeader {
    /// Reads the 4-byte signature field from a raw `AcpiTableHeader` pointer.
    ///
    /// # Safety
    ///
    /// `ptr` must point to a region of at least 4 bytes that is valid for reads.
    pub unsafe fn read_signature_from_ptr(ptr: *const Self) -> u32 {
        // SAFETY: Caller guarantees `ptr` points to at least 4 readable bytes.
        unsafe { ptr::read_unaligned(ptr::addr_of!((*ptr).signature)) }
    }

    /// Reads the 4-byte length field from a raw `AcpiTableHeader` pointer.
    ///
    /// # Safety
    ///
    /// `ptr` must point to a region of at least 8 bytes that is valid for reads.
    pub unsafe fn read_length_from_ptr(ptr: *const Self) -> u32 {
        // SAFETY: Caller guarantees `ptr` points to at least 8 readable bytes.
        unsafe { ptr::read_unaligned(ptr::addr_of!((*ptr).length)) }
    }

    /// Serialize an `AcpiTableHeader` into a `Vec<u8>` in ACPI's canonical layout.
    pub fn hdr_to_bytes(&self) -> Vec<u8> {
        // Pre‑allocate exactly the right length
        let mut buf = Vec::with_capacity(mem::size_of::<Self>());

        // Signature (4 bytes)
        buf.extend_from_slice(&self.signature.to_le_bytes());

        // Length (4 bytes, little‑endian)
        buf.extend_from_slice(&self.length.to_le_bytes());

        // Revision (1 byte), Checksum (1 byte)
        buf.push(self.revision);
        buf.push(self.checksum);

        // OEM ID (6 bytes)
        buf.extend_from_slice(&self.oem_id);

        // OEM Table ID (8 bytes)
        buf.extend_from_slice(&self.oem_table_id);

        // OEM Revision (4 bytes, little‑endian)
        buf.extend_from_slice(&self.oem_revision.to_le_bytes());

        // Creator ID (4 bytes, little‑endian)
        buf.extend_from_slice(&self.creator_id.to_le_bytes());

        // Creator Revision (4 bytes, little‑endian)
        buf.extend_from_slice(&self.creator_revision.to_le_bytes());

        buf
    }

    pub fn signature(&self) -> u32 {
        self.signature
    }

    pub fn length(&self) -> u32 {
        self.length
    }

    pub fn oem_revision(&self) -> u32 {
        self.oem_revision
    }

    pub fn creator_id(&self) -> u32 {
        self.creator_id
    }

    pub fn creator_revision(&self) -> u32 {
        self.creator_revision
    }
}

// SAFETY: `AcpiTableHeader` is itself a valid ACPI table header
unsafe impl crate::table::AcpiTable for AcpiTableHeader {
    const SIGNATURE: u32 = 0;

    type Fields = ();
    type Element = ();
    type Kind = crate::table::Fixed;
}
