//! Platform OEM identity information.
//!
//! ## License
//!
//! Copyright (C) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0

/// Platform identity fields shared by firmware-generated industry-standard tables.
///
/// Platforms can register this value as a component configuration and reuse it for ACPI and other
/// tables that carry the same OEM and creator identity.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct OemInfo {
    /// Platform vendor identifier.
    pub oem_id: [u8; 6],
    /// OEM-defined table or product identifier.
    pub oem_table_id: [u8; 8],
    /// OEM-defined platform revision.
    pub oem_revision: u32,
    /// Identifier of the utility that created the table.
    pub creator_id: u32,
    /// Revision of the utility that created the table.
    pub creator_revision: u32,
}

impl OemInfo {
    /// Creates platform OEM identity information.
    pub const fn new(
        oem_id: [u8; 6],
        oem_table_id: [u8; 8],
        oem_revision: u32,
        creator_id: u32,
        creator_revision: u32,
    ) -> Self {
        Self { oem_id, oem_table_id, oem_revision, creator_id, creator_revision }
    }
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
mod tests {
    use super::*;

    #[test]
    fn test_oem_info_new_sets_all_fields() {
        let information = OemInfo::new(*b"OEM_ID", *b"TABLE_ID", 1, 2, 3);

        assert_eq!(information.oem_id, *b"OEM_ID");
        assert_eq!(information.oem_table_id, *b"TABLE_ID");
        assert_eq!(information.oem_revision, 1);
        assert_eq!(information.creator_id, 2);
        assert_eq!(information.creator_revision, 3);
    }
}
