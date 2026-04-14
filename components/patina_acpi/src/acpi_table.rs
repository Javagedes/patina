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

use crate::{
    error::AcpiError, service::AcpiTable, signature::ACPI_CHECKSUM_OFFSET,
};
use alloc::{rc::Rc, boxed::Box, alloc::Allocator};

use core::{
    any::TypeId,
    fmt::Debug,
    mem,
    ptr,
};

use zerocopy_derive::*;

unsafe impl AcpiTable for AcpiFadt {}

/// Represents the FADT for ACPI 2.0+.
/// Equivalent to EFI_ACPI_3_0_FIXED_ACPI_DESCRIPTION_TABLE.
#[repr(C, packed)]
#[derive(Default, FromBytes, IntoBytes, KnownLayout, Immutable)]
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
#[derive(Default, Clone, Debug, FromBytes, IntoBytes, KnownLayout, Immutable)]
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
#[derive(Debug, Clone, Default, Copy, FromBytes, IntoBytes, KnownLayout, Immutable)]
pub struct GenericAddressStructure {
    address_space_id: u8,
    register_bit_width: u8,
    register_bit_offset: u8,
    access_size: u8,
    address: u64,
}

unsafe impl AcpiTable for AcpiFacs {}

/// Represents the FACS for ACPI 2.0+.
/// Note that the FACS does not have a standard ACPI header.
/// The FACS is not present in the list of installed ACPI tables; instead, it is only accessible through the FADT's `x_firmware_ctrl` field.
/// The FACS is always allocated in NVS, and is required to be 64B-aligned.
/// Equivalent to EFI_ACPI_3_0_FIRMWARE_ACPI_CONTROL_STRUCTURE.
#[repr(C, packed)]
#[derive(Default, Clone, FromBytes, IntoBytes, KnownLayout, Immutable)]
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

impl AcpiFacs {

}

/// Represents the DSDT for ACPI 2.0+.
/// The DSDT is not present in the list of installed ACPI tables; instead, it is only accessible through the FADT's `x_dsdt` field.
/// The DSDT has a standard header followed by variable-length AML bytecode.
/// The `length` field of the header tells us the number of trailing bytes representing bytecode.
#[repr(C, packed)]
#[derive(Default, FromBytes, IntoBytes, KnownLayout, Immutable)]
pub struct AcpiDsdt {
    pub(crate) header: AcpiTableHeader,
}

/// Represents the RSDP for ACPI 2.0+.
/// The RSDP is not a standard ACPI table and does not have a standard header.
/// It is not present in the list of installed tables and is not directly accessible.
/// Equivalent to EFI_ACPI_3_0_ROOT_SYSTEM_DESCRIPTION_POINTER.
#[repr(C, packed)]
#[derive(Default, FromBytes, IntoBytes, KnownLayout, Immutable)]
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
#[derive(Default)]
pub struct AcpiXsdt {
    pub(crate) header: AcpiTableHeader,
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

unsafe impl AcpiTable for AcpiTableHeader {}
/// Represents a standard ACPI header.
/// Equivalent to EFI_ACPI_DESCRIPTION_HEADER.
#[repr(C, packed)]
#[derive(Default, Clone, Debug, FromBytes, IntoBytes, Immutable, KnownLayout)]
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

#[derive(Clone, Debug)]
pub struct Table<A: Allocator = &'static dyn alloc::alloc::Allocator> {
    pub(crate) data: Rc<[u8], A>,
    pub(crate) type_id: core::any::TypeId,
}

impl Table<alloc::alloc::Global> {
    pub fn new<T: AcpiTable + 'static>(table: T) -> Result<Self, AcpiError> {
        Self::new_in(table, alloc::alloc::Global)
    }
}

impl<A: Allocator> Table<A> {
    pub fn new_in<T: AcpiTable + 'static>(table: T, alloc: A) -> Result<Self, AcpiError> {
        let len = table.header().length as usize;

        let table = Self::new_in_from_bytes(table.as_bytes(), alloc)?.with_type_id::<T>();

        if table.as_bytes().len() != len {
            return Err(AcpiError::InvalidTableFormat);
        }

        Ok(table)
    }

    fn with_type_id<T: 'static>(mut self) -> Self {
        self.type_id = TypeId::of::<T>();
        self
    }

    fn new_in_from_bytes(bytes: &[u8], alloc: A) -> Result<Self, AcpiError> {
        let len = bytes.len();
        let mut rc = Rc::new_zeroed_slice_in(len, alloc);

        // SAFETY: src is valid for reads of bytes.len() as the data comes from the byte slice.
        // SAFETY: dst is valid for writes of bytes.len() as it was just allocated with that length above.
        // SAFETY: the underlying data is a `u8` so there are no alignment concerns.
        // SAFETY: src and dst do not overlap.
        let rc = unsafe {
            ptr::copy_nonoverlapping(
                bytes.as_ptr(),
                Rc::get_mut(&mut rc).expect("Owned").as_mut_ptr().cast::<u8>(),
                len,
            );
            // SAFETY: The above copy initializes the Rc with valid data
            rc.assume_init()
        };

        Ok(Self { data: rc, type_id: TypeId::of::<AcpiTableHeader>() })
    }

    /// Creates a new Table from a raw pointer.
    /// When created this way, the type of the table is unknown.
    ///
    /// ## Safety
    ///
    /// - Caller must ensure the pointer refers to a valid ACPI table.
    /// - Caller must ensure `table_length` correctly specify the length of the table, including the header and any trailing data bytes.
    pub(crate) unsafe fn new_from_ptr(
        header_ptr: *const AcpiTableHeader,
        alloc: A,
    ) -> Result<Self, AcpiError> {
        if header_ptr.is_null() {
            return Err(AcpiError::NullTablePtr);
        }
        // TODO: FACS needs its own special handling outside of these APIs because it needs to be allocated in the lower 32-bit address space. This is a workaround for Windows' reliance on the legacy 32-bit FACS pointer in the FADT, and can be removed when Windows no longer relies on this field.
        // TODO: UEFI signature needs to use ACPIMemoryNVS

        // SAFETY: src is valid for reads due to caller unsafe contract.
        // SAFETY: src points to a valid ACPI Table header per caller unsafe contract.
        let header: AcpiTableHeader = unsafe { ptr::read_unaligned(header_ptr) };
        let len = header.length as usize;

        // SAFETY: data is non-null via validation above
        // SAFETY: data is valid for reads of `len` bytes due to caller unsafe contract and correct length specification.
        let bytes = unsafe { core::slice::from_raw_parts(header_ptr as *const u8, len) };
        return Self::new_in_from_bytes(bytes, alloc)
    }

    pub fn signature(&self) -> u32 {
        self.header().signature()
    }

    pub fn header(&self) -> &AcpiTableHeader {
        <AcpiTableHeader as zerocopy::FromBytes>::ref_from_prefix(self.data.as_ref()).unwrap().0
    }

    pub fn header_mut(&mut self) -> Option<&mut AcpiTableHeader> {
        <AcpiTableHeader as zerocopy::FromBytes>::mut_from_prefix(self.as_bytes_mut()?).map(|(header, _)| header).ok()
    }

    /// Returns the bytes of the entire table
    pub fn as_bytes(&self) -> &[u8] {
        self.data.as_ref()
    }

    pub fn as_bytes_mut(&mut self) -> Option<&mut [u8]> {
        Rc::get_mut(&mut self.data).map(|bytes| bytes.as_mut())
    }

    /// Updates the checksum for an ACPI table.
    /// According to the ACPI spec 2.0+, all bytes of a table must sum to zero modulo 256.
    pub(crate) fn update_checksum(&mut self) -> Result<(), AcpiError> {
        // SAFETY: The construction of `AcpiTable` maintains that `self.length` is the size in memory.
        let len = self.as_bytes().len();

        // Set the checksum field (byte at the specified `offset`) to zero before recalculation.
        if len > ACPI_CHECKSUM_OFFSET {
            self.header_mut().unwrap().checksum = 0;

            // Recalculate checksum.
            let sum: u8 = self.as_bytes().iter().fold(0u8, |sum, &b| sum.wrapping_add(b));
            self.header_mut().unwrap().checksum = (0u8).wrapping_sub(sum);
            Ok(())
        } else {
            Err(AcpiError::InvalidChecksumOffset)
        }
    }

    /// Returns a reference to the entire AcpiTable.
    pub fn as_ref<T: AcpiTable>(&self) -> &T {
        T::ref_from_bytes(self.as_bytes()).unwrap()
    }

    /// Returns a mutable reference to the entire AcpiTable.
    pub(crate) fn as_mut<T: AcpiTable>(&mut self) -> Option<&mut T> {
        T::mut_from_bytes(self.as_bytes_mut()?).ok()
    }

    /// Returns a pointer to the underlying AcpiTable.
    pub(crate) fn as_ptr(&self) -> *const AcpiTableHeader {
        self.header() as *const _
    }

    /// Returns a mutable pointer to the underlying AcpiTable.
    pub(crate) fn as_mut_ptr(&self) -> *mut AcpiTableHeader {
        self.header() as *const _ as *mut _
    }
}

#[cfg(test)]
mod tests {
    use patina::{component::service::{Service, memory::{MemoryManager, StdMemoryManager}}, efi_types::EfiMemoryType};

    use super::*;
    use core::mem;

    unsafe impl AcpiTable for TestTable {}
    #[repr(C)]
    #[derive(IntoBytes, FromBytes, KnownLayout, Immutable)]
    struct TestTable {
        header: AcpiTableHeader,
        body: [u8; 3],
    }

    const TEST_SIGNATURE: u32 = 0x123;

    #[test]
    fn test_update_checksum_on_real_acpi_table() {
        // Build a mock table.
        let test_table = TestTable {
            header: AcpiTableHeader {
                signature: TEST_SIGNATURE,
                length: (mem::size_of::<TestTable>()) as u32,
                revision: 1,
                checksum: 0, // we'll fill this
                oem_id: [0; 6],
                oem_table_id: *b"TBL_ID__",
                oem_revision: 0xAABBCCDD,
                creator_id: 0x11223344,
                creator_revision: 0x55667788,
            },
            body: [10, 20, 30], // some payload bytes
        };

        let mut acpi_table = Table::new(test_table).unwrap();

        // Update the checksum (use standard checksum offset since it has a standard header).
        assert!(acpi_table.update_checksum().is_ok());

        // Pull out the bytes and verify the checksum.
        // SAFETY: The table length is correctly specified in the test header.
        let bytes = acpi_table.as_bytes();
        // Total sum must be zero mod 256.
        let total: u8 = bytes.iter().copied().fold(0u8, |acc, b| acc.wrapping_add(b));
        assert_eq!(total, 0, "entire table did not sum to zero");
    }

    #[test]
    fn test_new_from_ptr_creates_valid_acpi_table() {
        // Build a mock table.
        let test_table = TestTable {
            header: AcpiTableHeader {
                signature: TEST_SIGNATURE,
                length: (mem::size_of::<TestTable>()) as u32,
                revision: 2,
                checksum: 0,
                oem_id: [1, 2, 3, 4, 5, 6],
                oem_table_id: *b"test_tes",
                oem_revision: 0xDEADBEEF,
                creator_id: 0xCAFEBABE,
                creator_revision: 0xFEEDFACE,
            },
            body: [42, 43, 44],
        };

        // Allocate the table on the heap.
        let boxed = Box::new(test_table);
        let raw_ptr = Box::into_raw(boxed);

        let mm: Service<dyn MemoryManager> = Service::mock(Box::new(StdMemoryManager::new()));
        let alloc = mm.get_allocator(EfiMemoryType::ACPIReclaimMemory).unwrap();

        // SAFETY: raw_ptr points to a valid TestTable with a valid header.
        let acpi_table =
            unsafe { Table::new_from_ptr(raw_ptr as *const AcpiTableHeader, mm.get_allocator(EfiMemoryType::ACPIReclaimMemory).unwrap()) }
                .unwrap();

        // Check signature and header fields.
        assert_eq!(acpi_table.signature(), TEST_SIGNATURE);
        let header = acpi_table.header();
        assert_eq!(header.length(), mem::size_of::<TestTable>() as u32);
        assert_eq!(header.revision, 2);
        assert_eq!(header.oem_id, [1, 2, 3, 4, 5, 6]);
        assert_eq!(header.oem_table_id, *b"test_tes");
        assert_eq!(header.oem_revision(), 0xDEADBEEF);
        assert_eq!(header.creator_id(), 0xCAFEBABE);
        assert_eq!(header.creator_revision(), 0xFEEDFACE);
        assert_eq!(acpi_table.as_ref::<TestTable>().body, [42, 43, 44]);

        // Check that the body bytes are correct.
        let bytes = acpi_table.as_bytes();
        let body_offset = mem::size_of::<AcpiTableHeader>();
        assert_eq!(&bytes[body_offset..body_offset + 3], &[42, 43, 44]);

        // Verify new_from_ptr correctly copies trailing data beyond the struct.
        let trailing: &[u8] = &[0xAA, 0xBB, 0xCC, 0xDD];
        let struct_size = mem::size_of::<TestTable>();
        let total_len = struct_size + trailing.len();
        let mut buf = vec![0u8; total_len];

        // SAFETY: raw_ptr still points to the heap-allocated TestTable from above.
        unsafe {
            ptr::copy_nonoverlapping(raw_ptr as *const u8, buf.as_mut_ptr(), struct_size);
        }
        // Follow up with the trailing data.
        buf[struct_size..].copy_from_slice(trailing);
        // Patch the length field to cover the trailing data.
        buf[4..8].copy_from_slice(&(total_len as u32).to_le_bytes());

        // SAFETY: buf points to a contiguous buffer of total_len bytes with a valid header.
        let table_with_trailing =
            unsafe { Table::new_from_ptr(buf.as_ptr() as *const AcpiTableHeader, alloc) }.unwrap();
        assert_eq!(table_with_trailing.header().length(), total_len as u32);

        let all_bytes = table_with_trailing.as_bytes();
        assert_eq!(&all_bytes[struct_size..], trailing);
    }

    #[test]
    fn test_new_rejects_length_greater_than_struct_size() {
        let header = AcpiTableHeader { signature: TEST_SIGNATURE, length: 100, ..Default::default() };
        let result = Table::new(header);
        assert!(matches!(result, Err(AcpiError::InvalidTableFormat)));
    }

    #[test]
    fn test_new_rejects_length_less_than_struct_size() {
        let header = AcpiTableHeader { signature: TEST_SIGNATURE, length: 10, ..Default::default() };

        // length < size_of::<AcpiTableHeader>(), so it should be rejected.
        let result = Table::new(header);
        assert!(matches!(result, Err(AcpiError::InvalidTableFormat)));
    }
}
