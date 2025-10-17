//! SMBIOS service interfaces
//!
//! This module defines the public service types for SMBIOS operations.
//! These are the primary interfaces that platform code uses to interact with SMBIOS.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!

extern crate alloc;
use alloc::vec::Vec;
use core::cell::Ref;
use r_efi::efi::Handle;
use zerocopy_derive::{FromBytes, Immutable, IntoBytes as DeriveIntoBytes, KnownLayout};

/// SMBIOS record handle type (16-bit identifier)
pub type SmbiosHandle = u16;

/// SMBIOS record type
pub type SmbiosType = u8;

/// Special handle value for automatic assignment
pub const SMBIOS_HANDLE_PI_RESERVED: SmbiosHandle = 0xFFFE;

/// SMBIOS string maximum length per specification
pub const SMBIOS_STRING_MAX_LENGTH: usize = 64;

/// SMBIOS table header structure
///
/// This is the standard 4-byte header that appears at the start of every SMBIOS record.
/// It contains the record type, length of structured data, and a unique handle.
#[repr(C, packed)]
#[derive(Debug, Clone, PartialEq, FromBytes, DeriveIntoBytes, Immutable, KnownLayout)]
pub struct SmbiosTableHeader {
    /// SMBIOS record type
    pub record_type: SmbiosType,
    /// Length of the structured data (including header)
    pub length: u8,
    /// Unique handle for this record
    pub handle: SmbiosHandle,
}

impl SmbiosTableHeader {
    /// Creates a new SMBIOS table header
    pub fn new(record_type: SmbiosType, length: u8, handle: SmbiosHandle) -> Self {
        Self { record_type, length, handle }
    }
}

/// Iterator over SMBIOS records
///
/// This iterator is used internally by the SMBIOS manager for:
/// - C protocol `GetNext` implementation (EDKII compatibility)
/// - Internal iteration during table publication
/// - Test validation
///
/// **Note:** This iterator is not exposed through the public `Service<Smbios>` API.
/// Platform code typically adds records using `add_record<T>()` and then publishes
/// the table for the OS to query directly.
///
/// # Type Filtering
///
/// The iterator can optionally filter by record type. If `None` is provided,
/// all records are returned. If `Some(type)` is provided, only records of
/// that type are returned.
pub struct SmbiosRecordsIter<'a> {
    records: Ref<'a, Vec<crate::manager::SmbiosRecord>>,
    position: usize,
    filter_type: Option<SmbiosType>,
}

impl<'a> SmbiosRecordsIter<'a> {
    /// Create a new iterator over SMBIOS records
    pub(crate) fn new(records: Ref<'a, Vec<crate::manager::SmbiosRecord>>, filter_type: Option<SmbiosType>) -> Self {
        Self { records, position: 0, filter_type }
    }
}

impl<'a> Iterator for SmbiosRecordsIter<'a> {
    type Item = (SmbiosTableHeader, Option<Handle>);

    fn next(&mut self) -> Option<Self::Item> {
        while self.position < self.records.len() {
            let record = &self.records[self.position];
            self.position += 1;

            // Apply type filter if specified
            if let Some(filter) = self.filter_type
                && record.header.record_type != filter
            {
                continue;
            }

            return Some((record.header.clone(), record.producer_handle));
        }

        None
    }
}

/// SMBIOS service providing all SMBIOS operations
///
/// This service provides a complete interface for SMBIOS table management:
/// - **Type-safe operations**: `add_record<T>()` for structured record types (recommended)
/// - **Record management**: `update_string()`, `remove()`
/// - **Table management**: `version()`, `publish_table()`
///
/// All operations are protected by a TplMutex at TPL_NOTIFY level for thread safety.
///
/// # Example
///
/// ```ignore
/// fn entry_point(
///     smbios: Service<Smbios>,
/// ) -> Result<()> {
///     // Add structured records
///     smbios.add_record(None, &bios_info)?;
///     
///     // Publish to configuration table
///     smbios.publish_table()?;
///     Ok(())
/// }
/// ```
#[derive(patina::component::service::IntoService)]
#[service(Smbios)]
pub struct Smbios {
    pub(crate) manager: patina::tpl_mutex::TplMutex<
        'static,
        crate::manager::SmbiosManager,
        patina::boot_services::StandardBootServices,
    >,
    pub(crate) boot_services: &'static patina::boot_services::StandardBootServices,
    pub(crate) major_version: u8,
    pub(crate) minor_version: u8,
}

// Methods below are tested via integration (Q35 platform component)
// They require StandardBootServices and TplMutex which aren't mockable in unit tests
#[cfg_attr(coverage_nightly, coverage(off))]
impl Smbios {
    /// Gets the SMBIOS version information.
    ///
    /// # Returns
    ///
    /// A tuple of (major_version, minor_version).
    pub fn version(&self) -> (u8, u8) {
        (self.major_version, self.minor_version)
    }

    /// Publishes the SMBIOS table to the UEFI Configuration Table
    ///
    /// This should be called after all records have been added and the table
    /// is ready to be consumed by the operating system or other firmware components.
    ///
    /// # Returns
    ///
    /// Returns a tuple of (table_address, entry_point_address) on success:
    /// - `table_address`: Physical address of the SMBIOS table data
    /// - `entry_point_address`: Physical address of the SMBIOS 3.x entry point structure
    ///
    /// # Errors
    ///
    /// Returns `SmbiosError` if:
    /// - No records have been added
    /// - Memory allocation fails
    /// - Configuration table installation fails
    pub fn publish_table(
        &self,
    ) -> core::result::Result<(r_efi::efi::PhysicalAddress, r_efi::efi::PhysicalAddress), crate::error::SmbiosError>
    {
        let manager = self.manager.lock();
        manager.publish_table(self.boot_services)
    }

    /// Updates a string in an existing SMBIOS record.
    ///
    /// # Arguments
    ///
    /// * `smbios_handle` - Handle of the record to update
    /// * `string_number` - 1-based index of the string to update
    /// * `string` - New string value
    pub fn update_string(
        &self,
        smbios_handle: SmbiosHandle,
        string_number: usize,
        string: &str,
    ) -> core::result::Result<(), crate::error::SmbiosError> {
        let manager = self.manager.lock();
        manager.update_string(smbios_handle, string_number, string)
    }

    /// Removes an SMBIOS record from the SMBIOS table.
    ///
    /// # Arguments
    ///
    /// * `smbios_handle` - Handle of the record to remove
    pub fn remove(&self, smbios_handle: SmbiosHandle) -> core::result::Result<(), crate::error::SmbiosError> {
        let manager = self.manager.lock();
        manager.remove(smbios_handle)
    }

    /// Add an SMBIOS record from a structured type.
    ///
    /// This is a type-safe convenience method that automatically serializes
    /// a structured record and adds it to the SMBIOS table.
    ///
    /// # Arguments
    ///
    /// * `producer_handle` - Optional handle of the producer creating this record
    /// * `record` - A reference to any type implementing `SmbiosRecordStructure`
    ///
    /// # Returns
    ///
    /// Returns the assigned SMBIOS handle for the newly added record.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let bios_info = Type0PlatformFirmwareInformation { ... };
    /// let handle = smbios.add_record(None, &bios_info)?;
    /// ```
    pub fn add_record<T>(
        &self,
        producer_handle: Option<r_efi::efi::Handle>,
        record: &T,
    ) -> core::result::Result<SmbiosHandle, crate::error::SmbiosError>
    where
        T: crate::smbios_record::SmbiosRecordStructure,
    {
        let bytes = record.to_bytes();
        // Delegate to the manager
        let manager = self.manager.lock(); // TPL raised to NOTIFY
        manager.add_from_bytes(producer_handle, &bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    extern crate std;
    use std::format;

    #[test]
    fn test_smbios_table_header_new() {
        let header = SmbiosTableHeader::new(0, 24, 0x0001);
        assert_eq!(header.record_type, 0);
        assert_eq!(header.length, 24);
        // Use local variable to avoid packed field alignment issues
        let handle = header.handle;
        assert_eq!(handle, 0x0001);
    }

    #[test]
    fn test_smbios_table_header_clone() {
        let header1 = SmbiosTableHeader::new(1, 32, 0x0002);
        let header2 = header1.clone();
        assert_eq!(header1, header2);
    }

    #[test]
    fn test_smbios_table_header_debug() {
        let header = SmbiosTableHeader::new(127, 4, 0xFFFF);
        let debug_str = format!("{:?}", header);
        assert!(debug_str.contains("127"));
        assert!(debug_str.contains("4"));
    }

    #[test]
    fn test_smbios_handle_pi_reserved() {
        assert_eq!(SMBIOS_HANDLE_PI_RESERVED, 0xFFFE);
    }

    #[test]
    fn test_smbios_string_max_length() {
        assert_eq!(SMBIOS_STRING_MAX_LENGTH, 64);
    }

    #[test]
    fn test_smbios_table_header_equality() {
        let header1 = SmbiosTableHeader::new(0, 24, 0x0001);
        let header2 = SmbiosTableHeader::new(0, 24, 0x0001);
        let header3 = SmbiosTableHeader::new(1, 24, 0x0001);

        assert_eq!(header1, header2);
        assert_ne!(header1, header3);
    }

    #[test]
    fn test_smbios_table_header_from_bytes() {
        use zerocopy::IntoBytes;
        let header = SmbiosTableHeader::new(127, 4, 0xFFFE);
        let bytes = header.as_bytes();
        assert_eq!(bytes.len(), 4);
        assert_eq!(bytes[0], 127); // type
        assert_eq!(bytes[1], 4); // length
    }

    #[test]
    fn test_smbios_records_iter_basic() {
        use crate::manager::SmbiosRecord;
        use alloc::vec;
        use core::cell::RefCell;

        let records = RefCell::new(vec![
            SmbiosRecord::new(SmbiosTableHeader::new(0, 24, 0x0001), None, vec![], 0),
            SmbiosRecord::new(SmbiosTableHeader::new(1, 32, 0x0002), None, vec![], 0),
        ]);

        let borrowed = records.borrow();
        let mut iter = SmbiosRecordsIter::new(borrowed, None);

        let first = iter.next().unwrap();
        assert_eq!(first.0.record_type, 0);
        let handle = first.0.handle;
        assert_eq!(handle, 0x0001);

        let second = iter.next().unwrap();
        assert_eq!(second.0.record_type, 1);
        let handle = second.0.handle;
        assert_eq!(handle, 0x0002);

        assert!(iter.next().is_none());
    }

    #[test]
    fn test_smbios_records_iter_with_filter() {
        use crate::manager::SmbiosRecord;
        use alloc::vec;
        use core::cell::RefCell;

        let records = RefCell::new(vec![
            SmbiosRecord::new(SmbiosTableHeader::new(0, 24, 0x0001), None, vec![], 0),
            SmbiosRecord::new(SmbiosTableHeader::new(1, 32, 0x0002), None, vec![], 0),
            SmbiosRecord::new(SmbiosTableHeader::new(0, 24, 0x0003), None, vec![], 0),
        ]);

        let borrowed = records.borrow();
        let mut iter = SmbiosRecordsIter::new(borrowed, Some(0));

        let first = iter.next().unwrap();
        assert_eq!(first.0.record_type, 0);
        let handle = first.0.handle;
        assert_eq!(handle, 0x0001);

        let second = iter.next().unwrap();
        assert_eq!(second.0.record_type, 0);
        let handle = second.0.handle;
        assert_eq!(handle, 0x0003);

        assert!(iter.next().is_none());
    }

    #[test]
    fn test_smbios_records_iter_empty() {
        use crate::manager::SmbiosRecord;
        use alloc::vec;
        use core::cell::RefCell;

        let records: RefCell<Vec<SmbiosRecord>> = RefCell::new(vec![]);
        let borrowed = records.borrow();
        let mut iter = SmbiosRecordsIter::new(borrowed, None);

        assert!(iter.next().is_none());
    }

    #[test]
    fn test_smbios_records_iter_no_match_filter() {
        use crate::manager::SmbiosRecord;
        use alloc::vec;
        use core::cell::RefCell;

        let records = RefCell::new(vec![
            SmbiosRecord::new(SmbiosTableHeader::new(0, 24, 0x0001), None, vec![], 0),
            SmbiosRecord::new(SmbiosTableHeader::new(1, 32, 0x0002), None, vec![], 0),
        ]);

        let borrowed = records.borrow();
        let mut iter = SmbiosRecordsIter::new(borrowed, Some(127)); // Filter for type 127

        assert!(iter.next().is_none());
    }
}
