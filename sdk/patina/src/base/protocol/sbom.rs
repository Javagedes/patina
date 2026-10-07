//! Software Bill of Materials discovery protocol.
//!
//! ## License
//!
//! Copyright (C) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0

use super::ProtocolInterface;

/// Protocol interface for one serialized SBOM ACPI table entry.
///
/// The interface pointer is the address of the complete serialized
/// [`SbomTableEntry`](crate::acpi::SbomTableEntry), matching the HII package-list protocol pattern.
/// This alias names its fixed-size prefix so UEFI protocol discovery can use a thin pointer; the
/// payload bytes immediately follow the header.
pub type SbomProtocol = crate::acpi::SbomTableEntryHeader;

// SAFETY: An interface installed under this GUID points to a complete serialized
// `SbomTableEntry`, whose first field is `SbomTableEntryHeader`.
unsafe impl ProtocolInterface for SbomProtocol {
    const PROTOCOL_GUID: crate::BinaryGuid = crate::BinaryGuid::from_string("6F84698B-C4E9-4BD0-9C8F-5EB6C6F46871");
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
mod tests {
    use super::*;

    #[test]
    fn test_sbom_protocol_guid() {
        assert_eq!(
            <SbomProtocol as ProtocolInterface>::PROTOCOL_GUID,
            crate::BinaryGuid::from_string("6F84698B-C4E9-4BD0-9C8F-5EB6C6F46871")
        );
    }
}
