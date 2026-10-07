//! Advanced Configuration and Power Interface (ACPI) definitions.
//!
//! ## License
//!
//! Copyright (C) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0

use core::{fmt, iter::FusedIterator, mem::size_of};

use zerocopy::{Immutable, IntoBytes, KnownLayout, TryFromBytes};

/// Signature for the Software Bill of Materials (SBOM) ACPI table.
pub const EFI_ACPI_SBOM_TABLE_SIGNATURE: u32 = crate::signature!('S', 'B', 'O', 'M');

/// Current revision of the SBOM ACPI table.
pub const EFI_ACPI_SBOM_TABLE_REVISION: u8 = 0x01;

/// No flags are set on the SBOM table entry.
pub const EFI_ACPI_SBOM_TABLE_ENTRY_FLAG_NONE: u8 = 0x00;

/// Reserved SBOM table entry flag.
pub const EFI_ACPI_SBOM_TABLE_ENTRY_FLAG_RESERVED: u8 = 0x01;

/// The SBOM payload uses the Concise Software Identification format.
pub const EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_FORMAT_COSWID: u8 = 0x00;

/// The SBOM payload uses the `CycloneDX` format.
pub const EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_FORMAT_CYCLONEDX: u8 = 0x01;

/// The SBOM payload uses the Software Package Data Exchange format.
pub const EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_FORMAT_SPDX: u8 = 0x02;

/// The SBOM payload uses a vendor-defined format.
pub const EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_FORMAT_VENDOR: u8 = 0xFF;

/// The SBOM payload is not compressed.
pub const EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_COMPRESSION_NONE: u8 = 0x00;

/// The SBOM payload uses zlib compression.
pub const EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_COMPRESSION_ZLIB: u8 = 0x01;

/// The SBOM payload uses LZMA compression.
pub const EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_COMPRESSION_LZMA: u8 = 0x02;

/// The SBOM payload uses a vendor-defined compression format.
pub const EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_COMPRESSION_VENDOR: u8 = 0xFF;

/// Current revision of an SBOM ACPI table entry.
pub const EFI_ACPI_SBOM_TABLE_ENTRY_REVISION: u8 = 0x04;

/// Length of the fixed SBOM ACPI table entry header.
pub const EFI_ACPI_SBOM_TABLE_ENTRY_HEADER_LENGTH: u16 = 0x000A;

/// Errors encountered while parsing an SBOM ACPI table or table entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SbomTableParseError {
    /// The input does not contain the number of bytes declared by the structure.
    BufferTooSmall {
        /// Required number of bytes.
        expected: usize,
        /// Available number of bytes.
        actual: usize,
    },
    /// The ACPI table signature is not `SBOM`.
    InvalidTableSignature {
        /// Signature found in the table header.
        signature: u32,
    },
    /// The ACPI table revision is not supported.
    UnsupportedTableRevision {
        /// Revision found in the table header.
        revision: u8,
    },
    /// The ACPI table length is smaller than its fixed header.
    InvalidTableLength {
        /// Length found in the table header.
        length: u32,
    },
    /// The SBOM table entry revision is not supported.
    UnsupportedEntryRevision {
        /// Revision found in the entry header.
        revision: u8,
    },
    /// The SBOM table entry header length does not match the supported layout.
    InvalidEntryHeaderLength {
        /// Header length found in the entry.
        length: u16,
    },
    /// A declared length cannot be represented or overflows the total structure length.
    LengthOverflow,
    /// The bytes do not conform to the packed Rust representation.
    InvalidLayout,
}

impl fmt::Display for SbomTableParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BufferTooSmall { expected, actual } => {
                write!(f, "SBOM data requires {expected} bytes, but only {actual} bytes are available")
            }
            Self::InvalidTableSignature { signature } => {
                write!(f, "invalid SBOM ACPI table signature: {signature:#010X}")
            }
            Self::UnsupportedTableRevision { revision } => {
                write!(f, "unsupported SBOM ACPI table revision: {revision:#04X}")
            }
            Self::InvalidTableLength { length } => write!(f, "invalid SBOM ACPI table length: {length}"),
            Self::UnsupportedEntryRevision { revision } => {
                write!(f, "unsupported SBOM ACPI table entry revision: {revision:#04X}")
            }
            Self::InvalidEntryHeaderLength { length } => {
                write!(f, "invalid SBOM ACPI table entry header length: {length}")
            }
            Self::LengthOverflow => f.write_str("SBOM structure length overflow"),
            Self::InvalidLayout => f.write_str("invalid SBOM packed structure layout"),
        }
    }
}

impl core::error::Error for SbomTableParseError {}

/// Standard ACPI description header (`EFI_ACPI_DESCRIPTION_HEADER`).
#[derive(Debug, Default, Clone, Copy, TryFromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C, packed)]
pub struct AcpiDescriptionHeader {
    /// Four-byte table signature.
    pub signature: u32,
    /// Total table length, including this header.
    pub length: u32,
    /// Table revision.
    pub revision: u8,
    /// Checksum of the complete table.
    pub checksum: u8,
    /// Original equipment manufacturer identifier.
    pub oem_id: [u8; 6],
    /// Original equipment manufacturer table identifier.
    pub oem_table_id: [u8; 8],
    /// Original equipment manufacturer revision.
    pub oem_revision: u32,
    /// Vendor identifier of the utility that created the table.
    pub creator_id: u32,
    /// Revision of the utility that created the table.
    pub creator_revision: u32,
}

/// SBOM ACPI table (`EFI_ACPI_SBOM_TABLE`).
///
/// The trailing [`Self::entries`] slice contains consecutive [`SbomTableEntry`] byte sequences.
#[derive(TryFromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C, packed)]
pub struct SbomTable {
    /// Standard ACPI table header.
    pub header: AcpiDescriptionHeader,
    /// Encoded SBOM table entries.
    pub entries: [u8],
}

impl SbomTable {
    /// Parses an SBOM ACPI table from the beginning of `bytes`.
    ///
    /// This first parses and validates the fixed ACPI header, then uses its declared table length
    /// to parse exactly one [`SbomTable`]. Bytes following that table are returned untouched.
    ///
    /// # Errors
    ///
    /// Returns [`SbomTableParseError`] if the fixed header is truncated, its signature or revision
    /// is unsupported, its declared length is invalid, or the complete table is not present.
    pub fn parse_prefix(bytes: &[u8]) -> Result<(&Self, &[u8]), SbomTableParseError> {
        let header_length = size_of::<AcpiDescriptionHeader>();
        let (header_bytes, _) = split_prefix(bytes, header_length)?;
        let header = <AcpiDescriptionHeader as TryFromBytes>::try_ref_from_bytes(header_bytes)
            .map_err(|_| SbomTableParseError::InvalidLayout)?;

        let signature = header.signature;
        let revision = header.revision;
        let table_length = header.length;

        if signature != EFI_ACPI_SBOM_TABLE_SIGNATURE {
            return Err(SbomTableParseError::InvalidTableSignature { signature });
        }
        if revision != EFI_ACPI_SBOM_TABLE_REVISION {
            return Err(SbomTableParseError::UnsupportedTableRevision { revision });
        }

        let table_length = usize::try_from(table_length).map_err(|_| SbomTableParseError::LengthOverflow)?;
        if table_length < header_length {
            return Err(SbomTableParseError::InvalidTableLength { length: header.length });
        }

        let (table_bytes, remaining) = split_prefix(bytes, table_length)?;
        let table =
            <Self as TryFromBytes>::try_ref_from_bytes(table_bytes).map_err(|_| SbomTableParseError::InvalidLayout)?;
        Ok((table, remaining))
    }

    /// Returns a non-allocating iterator over all entries in the table.
    ///
    /// The complete entry stream is validated before the iterator is returned. Therefore, a
    /// malformed entry prevents access to every entry rather than exposing a valid prefix followed
    /// by a parsing error.
    ///
    /// # Errors
    ///
    /// Returns [`SbomTableParseError`] if any entry is malformed or truncated.
    pub fn entries(&self) -> Result<SbomTableEntries<'_>, SbomTableParseError> {
        let entries = &self.entries;
        let mut remaining = entries;
        let mut count = 0;

        while !remaining.is_empty() {
            let (_, next) = SbomTableEntry::parse_prefix(remaining)?;
            remaining = next;
            count += 1;
        }

        Ok(SbomTableEntries { remaining: entries, remaining_count: count })
    }
}

/// Fixed header of an SBOM ACPI table entry.
///
/// This is the fixed-size prefix of `EFI_ACPI_SBOM_TABLE_ENTRY`.
#[derive(Debug, Clone, Copy, TryFromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C, packed)]
pub struct SbomTableEntryHeader {
    /// Entry structure revision.
    pub revision: u8,
    /// Length of the fixed entry header.
    pub header_length: u16,
    /// Length of the following entry payload in bytes.
    pub payload_length: u32,
    /// Entry flags.
    pub flags: u8,
    /// SBOM payload format.
    pub format: u8,
    /// SBOM payload compression format.
    pub compression: u8,
}

/// SBOM ACPI table entry (`EFI_ACPI_SBOM_TABLE_ENTRY`).
#[derive(TryFromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C, packed)]
pub struct SbomTableEntry {
    /// Fixed entry header.
    pub header: SbomTableEntryHeader,
    /// SBOM payload, which must be treated as potentially unaligned bytes.
    pub payload: [u8],
}

impl SbomTableEntry {
    /// Parses an SBOM table entry from the beginning of `bytes`.
    ///
    /// This first parses and validates the fixed entry header, then uses its payload length to
    /// parse exactly one [`SbomTableEntry`]. Bytes following that entry are returned untouched.
    ///
    /// # Errors
    ///
    /// Returns [`SbomTableParseError`] if the fixed header is truncated, its revision or header
    /// length is unsupported, its total length overflows, or the complete payload is not present.
    pub fn parse_prefix(bytes: &[u8]) -> Result<(&Self, &[u8]), SbomTableParseError> {
        let fixed_header_length = size_of::<SbomTableEntryHeader>();
        let (header_bytes, _) = split_prefix(bytes, fixed_header_length)?;
        let header = <SbomTableEntryHeader as TryFromBytes>::try_ref_from_bytes(header_bytes)
            .map_err(|_| SbomTableParseError::InvalidLayout)?;

        let revision = header.revision;
        let header_length = header.header_length;
        let payload_length = header.payload_length;

        if revision != EFI_ACPI_SBOM_TABLE_ENTRY_REVISION {
            return Err(SbomTableParseError::UnsupportedEntryRevision { revision });
        }
        if header_length != EFI_ACPI_SBOM_TABLE_ENTRY_HEADER_LENGTH {
            return Err(SbomTableParseError::InvalidEntryHeaderLength { length: header_length });
        }

        let payload_length = usize::try_from(payload_length).map_err(|_| SbomTableParseError::LengthOverflow)?;
        let entry_length =
            fixed_header_length.checked_add(payload_length).ok_or(SbomTableParseError::LengthOverflow)?;
        let (entry_bytes, remaining) = split_prefix(bytes, entry_length)?;
        let entry =
            <Self as TryFromBytes>::try_ref_from_bytes(entry_bytes).map_err(|_| SbomTableParseError::InvalidLayout)?;
        Ok((entry, remaining))
    }

    /// Returns the entry payload without allocating.
    ///
    /// The wire format does not specify padding between entries. Consumers must parse this byte
    /// slice without assuming an alignment greater than one.
    pub fn payload(&self) -> &[u8] {
        &self.payload
    }
}

/// A non-allocating iterator over validated [`SbomTableEntry`] values.
pub struct SbomTableEntries<'a> {
    remaining: &'a [u8],
    remaining_count: usize,
}

impl<'a> Iterator for SbomTableEntries<'a> {
    type Item = &'a SbomTableEntry;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining_count == 0 {
            return None;
        }

        let (entry, remaining) = SbomTableEntry::parse_prefix(self.remaining)
            .expect("SBOM entry stream was validated before iterator construction");
        self.remaining = remaining;
        self.remaining_count -= 1;
        Some(entry)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining_count, Some(self.remaining_count))
    }
}

impl ExactSizeIterator for SbomTableEntries<'_> {}
impl FusedIterator for SbomTableEntries<'_> {}

fn split_prefix(bytes: &[u8], length: usize) -> Result<(&[u8], &[u8]), SbomTableParseError> {
    bytes.split_at_checked(length).ok_or(SbomTableParseError::BufferTooSmall { expected: length, actual: bytes.len() })
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
mod tests {
    use core::mem::{align_of, align_of_val, size_of, size_of_val};

    use super::*;

    fn initialize_table_header(bytes: &mut [u8], table_length: u32) {
        bytes[..4].copy_from_slice(&EFI_ACPI_SBOM_TABLE_SIGNATURE.to_ne_bytes());
        bytes[4..8].copy_from_slice(&table_length.to_ne_bytes());
        bytes[8] = EFI_ACPI_SBOM_TABLE_REVISION;
    }

    #[test]
    fn test_acpi_description_header_layout_and_byte_conversion() {
        let header = AcpiDescriptionHeader {
            signature: EFI_ACPI_SBOM_TABLE_SIGNATURE,
            length: 36,
            revision: EFI_ACPI_SBOM_TABLE_REVISION,
            checksum: 0xA5,
            oem_id: *b"OEM_ID",
            oem_table_id: *b"TABLE_ID",
            oem_revision: 0x1122_3344,
            creator_id: 0x5566_7788,
            creator_revision: 0x99AA_BBCC,
        };

        assert_eq!(align_of::<AcpiDescriptionHeader>(), 1);
        assert_eq!(size_of::<AcpiDescriptionHeader>(), 36);

        let bytes = header.as_bytes();
        let parsed = AcpiDescriptionHeader::try_ref_from_bytes(bytes).expect("header bytes should be valid");
        assert_eq!(parsed.as_bytes(), bytes);
    }

    #[test]
    fn test_sbom_table_layout_and_byte_conversion() {
        let mut bytes = [0u8; 40];
        let table_length = 38;
        initialize_table_header(&mut bytes, table_length);
        bytes[36..38].copy_from_slice(&[0xAA, 0x55]);
        bytes[38..].copy_from_slice(&[0xCC, 0xDD]);

        let (table, remaining) = SbomTable::parse_prefix(&bytes).expect("SBOM table bytes should be valid");
        let signature = table.header.signature;
        let length = table.header.length;

        assert_eq!(signature, EFI_ACPI_SBOM_TABLE_SIGNATURE);
        assert_eq!(length, table_length);
        assert_eq!(&table.entries, &[0xAA, 0x55]);
        assert_eq!(remaining, &[0xCC, 0xDD]);
        assert_eq!(align_of_val(table), 1);
        assert_eq!(size_of_val(table), table_length as usize);
        assert_eq!(table.as_bytes(), &bytes[..table_length as usize]);
    }

    #[test]
    fn test_sbom_table_entry_layout_and_byte_conversion() {
        let bytes = [
            EFI_ACPI_SBOM_TABLE_ENTRY_REVISION,
            0x0A,
            0x00,
            0x03,
            0x00,
            0x00,
            0x00,
            EFI_ACPI_SBOM_TABLE_ENTRY_FLAG_NONE,
            EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_FORMAT_COSWID,
            EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_COMPRESSION_ZLIB,
            0x11,
            0x22,
            0x33,
            0xCC,
            0xDD,
        ];

        let (entry, remaining) = SbomTableEntry::parse_prefix(&bytes).expect("SBOM table entry bytes should be valid");
        let header = entry.header;
        let revision = header.revision;
        let header_length = header.header_length;
        let payload_length = header.payload_length;

        assert_eq!(size_of::<SbomTableEntryHeader>(), EFI_ACPI_SBOM_TABLE_ENTRY_HEADER_LENGTH as usize);
        assert_eq!(revision, EFI_ACPI_SBOM_TABLE_ENTRY_REVISION);
        assert_eq!(header_length, EFI_ACPI_SBOM_TABLE_ENTRY_HEADER_LENGTH);
        assert_eq!(payload_length, 3);
        assert_eq!(entry.payload(), &[0x11, 0x22, 0x33]);
        assert_eq!(remaining, &[0xCC, 0xDD]);
        assert_eq!(align_of_val(entry), 1);
        assert_eq!(size_of_val(entry), 13);
        assert_eq!(entry.as_bytes(), &bytes[..13]);
    }

    #[test]
    fn test_sbom_table_iterates_entries_without_allocation() {
        let first_entry = [
            EFI_ACPI_SBOM_TABLE_ENTRY_REVISION,
            0x0A,
            0x00,
            0x03,
            0x00,
            0x00,
            0x00,
            EFI_ACPI_SBOM_TABLE_ENTRY_FLAG_NONE,
            EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_FORMAT_COSWID,
            EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_COMPRESSION_NONE,
            0x11,
            0x22,
            0x33,
        ];
        let second_entry = [
            EFI_ACPI_SBOM_TABLE_ENTRY_REVISION,
            0x0A,
            0x00,
            0x02,
            0x00,
            0x00,
            0x00,
            EFI_ACPI_SBOM_TABLE_ENTRY_FLAG_RESERVED,
            EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_FORMAT_SPDX,
            EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_COMPRESSION_ZLIB,
            0xAA,
            0xBB,
        ];
        let mut bytes = [0u8; 61];
        let table_length = bytes.len() as u32;
        initialize_table_header(&mut bytes, table_length);
        bytes[36..49].copy_from_slice(&first_entry);
        // The first entry has an odd total length, so the second entry begins at an odd offset.
        bytes[49..].copy_from_slice(&second_entry);

        let (table, remaining) = SbomTable::parse_prefix(&bytes).expect("SBOM table should parse");
        assert!(remaining.is_empty());

        let mut entries = table.entries().expect("all table entries should validate");
        assert_eq!(entries.len(), 2);

        let first = entries.next().expect("first entry should be present");
        assert_eq!(first.payload(), &[0x11, 0x22, 0x33]);
        assert_eq!(entries.len(), 1);

        let second = entries.next().expect("second entry should be present");
        assert_eq!(second.payload(), &[0xAA, 0xBB]);
        assert_eq!(entries.len(), 0);
        assert!(entries.next().is_none());
        assert!(entries.next().is_none());
    }

    #[test]
    fn test_sbom_table_parser_rejects_invalid_headers() {
        assert!(matches!(
            SbomTable::parse_prefix(&[0; 35]),
            Err(SbomTableParseError::BufferTooSmall { expected: 36, actual: 35 })
        ));

        let mut bytes = [0u8; 36];
        initialize_table_header(&mut bytes, 36);
        bytes[..4].copy_from_slice(&0xDEAD_BEEFu32.to_ne_bytes());
        assert!(matches!(
            SbomTable::parse_prefix(&bytes),
            Err(SbomTableParseError::InvalidTableSignature { signature: 0xDEAD_BEEF })
        ));

        initialize_table_header(&mut bytes, 36);
        bytes[8] = EFI_ACPI_SBOM_TABLE_REVISION + 1;
        assert!(matches!(SbomTable::parse_prefix(&bytes), Err(SbomTableParseError::UnsupportedTableRevision { .. })));

        initialize_table_header(&mut bytes, 35);
        assert!(matches!(SbomTable::parse_prefix(&bytes), Err(SbomTableParseError::InvalidTableLength { length: 35 })));

        initialize_table_header(&mut bytes, 37);
        assert!(matches!(
            SbomTable::parse_prefix(&bytes),
            Err(SbomTableParseError::BufferTooSmall { expected: 37, actual: 36 })
        ));
    }

    #[test]
    fn test_sbom_entry_parser_rejects_invalid_headers() {
        assert!(matches!(
            SbomTableEntry::parse_prefix(&[0; 9]),
            Err(SbomTableParseError::BufferTooSmall { expected: 10, actual: 9 })
        ));

        let mut bytes = [0u8; 10];
        bytes[0] = EFI_ACPI_SBOM_TABLE_ENTRY_REVISION + 1;
        bytes[1..3].copy_from_slice(&EFI_ACPI_SBOM_TABLE_ENTRY_HEADER_LENGTH.to_ne_bytes());
        assert!(matches!(
            SbomTableEntry::parse_prefix(&bytes),
            Err(SbomTableParseError::UnsupportedEntryRevision { .. })
        ));

        bytes[0] = EFI_ACPI_SBOM_TABLE_ENTRY_REVISION;
        bytes[1..3].copy_from_slice(&(EFI_ACPI_SBOM_TABLE_ENTRY_HEADER_LENGTH + 1).to_ne_bytes());
        assert!(matches!(
            SbomTableEntry::parse_prefix(&bytes),
            Err(SbomTableParseError::InvalidEntryHeaderLength { .. })
        ));

        bytes[1..3].copy_from_slice(&EFI_ACPI_SBOM_TABLE_ENTRY_HEADER_LENGTH.to_ne_bytes());
        bytes[3..7].copy_from_slice(&1u32.to_ne_bytes());
        assert!(matches!(
            SbomTableEntry::parse_prefix(&bytes),
            Err(SbomTableParseError::BufferTooSmall { expected: 11, actual: 10 })
        ));
    }

    #[test]
    fn test_sbom_table_rejects_entire_entry_stream_when_one_entry_is_invalid() {
        let valid_entry = [
            EFI_ACPI_SBOM_TABLE_ENTRY_REVISION,
            0x0A,
            0x00,
            0x01,
            0x00,
            0x00,
            0x00,
            EFI_ACPI_SBOM_TABLE_ENTRY_FLAG_NONE,
            EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_FORMAT_COSWID,
            EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_COMPRESSION_NONE,
            0xAA,
        ];
        let mut bytes = [0u8; 56];
        let table_length = bytes.len() as u32;
        initialize_table_header(&mut bytes, table_length);
        bytes[36..47].copy_from_slice(&valid_entry);

        let (table, _) = SbomTable::parse_prefix(&bytes).expect("outer table should parse");
        assert!(matches!(table.entries(), Err(SbomTableParseError::BufferTooSmall { expected: 10, actual: 9 })));
    }

    #[test]
    fn test_sbom_constants_match_c_definitions() {
        assert_eq!(EFI_ACPI_SBOM_TABLE_ENTRY_FLAG_NONE, 0x00);
        assert_eq!(EFI_ACPI_SBOM_TABLE_ENTRY_FLAG_RESERVED, 0x01);
        assert_eq!(EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_FORMAT_COSWID, 0x00);
        assert_eq!(EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_FORMAT_CYCLONEDX, 0x01);
        assert_eq!(EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_FORMAT_SPDX, 0x02);
        assert_eq!(EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_FORMAT_VENDOR, 0xFF);
        assert_eq!(EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_COMPRESSION_NONE, 0x00);
        assert_eq!(EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_COMPRESSION_ZLIB, 0x01);
        assert_eq!(EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_COMPRESSION_LZMA, 0x02);
        assert_eq!(EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_COMPRESSION_VENDOR, 0xFF);
    }
}
