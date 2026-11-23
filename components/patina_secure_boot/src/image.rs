//! Bounds-checked Authenticode inputs using goblin PE/COFF headers and sections.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use alloc::vec::Vec;
use core::ops::Range;
use goblin::pe::{
    header::{Header, SIZEOF_COFF_HEADER, SIZEOF_PE_MAGIC},
    section_table::{SIZEOF_SECTION_TABLE, SectionTable},
};
use patina::{
    BinaryGuid,
    crypto::{
        error::{CryptoError, Result},
        hash::{Hash, HashAlgorithm},
    },
};
use zerocopy::{
    FromBytes,
    byteorder::{LittleEndian, U16, U32},
};
use zerocopy_derive::{Immutable, KnownLayout, Unaligned};

#[repr(C)]
#[derive(FromBytes, KnownLayout, Immutable, Unaligned)]
struct WinCertificateHeader {
    length: U32<LittleEndian>,
    revision: U16<LittleEndian>,
    certificate_type: U16<LittleEndian>,
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
#[path = "image_tests.rs"]
mod tests;

pub(crate) struct AuthenticodeImage<'a> {
    bytes: &'a [u8],
    ranges: Vec<Range<usize>>,
    certificates: &'a [u8],
    digests: Vec<(HashAlgorithm, Vec<u8>)>,
}

impl<'a> AuthenticodeImage<'a> {
    pub(crate) fn parse(bytes: &'a [u8]) -> Result<Self> {
        let invalid = || CryptoError::InvalidParameter;
        let header = Header::parse(bytes).map_err(|_| invalid())?;
        if header.signature != 0x0000_4550 {
            return Err(invalid());
        }
        let optional = header.optional_header.ok_or_else(invalid)?;
        let optional_start = (header.dos_header.pe_pointer as usize)
            .checked_add(SIZEOF_PE_MAGIC + SIZEOF_COFF_HEADER)
            .ok_or_else(invalid)?;
        let optional_end =
            optional_start.checked_add(header.coff_header.size_of_optional_header as usize).ok_or_else(invalid)?;
        let directory_start = optional_start
            .checked_add(match optional.standard_fields.magic {
                0x10b => 96,
                0x20b => 112,
                _ => return Err(invalid()),
            })
            .ok_or_else(invalid)?;
        let headers_end = optional.windows_fields.size_of_headers as usize;
        let section_end = optional_end
            .checked_add(
                usize::from(header.coff_header.number_of_sections)
                    .checked_mul(SIZEOF_SECTION_TABLE)
                    .ok_or_else(invalid)?,
            )
            .ok_or_else(invalid)?;
        if directory_start > optional_end || section_end > headers_end || headers_end > bytes.len() {
            return Err(invalid());
        }
        let checksum = optional_start.checked_add(64).ok_or_else(invalid)?;
        let mut ranges = Vec::new();
        ranges.push(0..checksum);
        let mut cert_start = bytes.len();
        let mut certificates = &bytes[bytes.len()..];
        if optional.windows_fields.number_of_rva_and_sizes > 4 {
            let security_entry = directory_start.checked_add(4 * 8).ok_or_else(invalid)?;
            let security_end = security_entry.checked_add(8).ok_or_else(invalid)?;
            if security_end > optional_end {
                return Err(invalid());
            }
            ranges.push(checksum + 4..security_entry);
            ranges.push(security_end..headers_end);
            if let Some(directory) = optional.data_directories.get_certificate_table() {
                if directory.size != 0 {
                    cert_start = directory.virtual_address as usize;
                    let cert_end = cert_start.checked_add(directory.size as usize).ok_or_else(invalid)?;
                    // Attribute certificates are file data, never RVAs. Reject ambiguous layouts.
                    if !cert_start.is_multiple_of(8) || cert_start < headers_end || cert_end != bytes.len() {
                        return Err(invalid());
                    }
                    certificates = bytes.get(cert_start..cert_end).ok_or_else(invalid)?;
                } else if directory.virtual_address != 0 {
                    return Err(invalid());
                }
            }
        } else {
            ranges.push(checksum + 4..headers_end);
        }
        let mut sections = Vec::new();
        let mut offset = optional_end;
        for _ in 0..header.coff_header.number_of_sections {
            let section = SectionTable::parse(bytes, &mut offset, 0).map_err(|_| invalid())?;
            if section.size_of_raw_data != 0 {
                let start = section.pointer_to_raw_data as usize;
                let end = start.checked_add(section.size_of_raw_data as usize).ok_or_else(invalid)?;
                if start < headers_end || end > cert_start {
                    return Err(invalid());
                }
                sections.push(start..end);
            }
        }
        sections.sort_unstable_by_key(|range| range.start);
        let mut previous_end = headers_end;
        let mut hashed_size = headers_end;
        for section in sections {
            if section.start < previous_end {
                return Err(invalid());
            }
            previous_end = section.end;
            hashed_size = hashed_size.checked_add(section.len()).ok_or_else(invalid)?;
            ranges.push(section);
        }
        if hashed_size > cert_start {
            return Err(invalid());
        }
        ranges.push(hashed_size..cert_start);
        if ranges.iter().any(|range| bytes.get(range.clone()).is_none()) {
            return Err(invalid());
        }
        Ok(Self { bytes, ranges, certificates, digests: Vec::new() })
    }

    pub(crate) fn digest(&mut self, hash: &dyn Hash, algorithm: HashAlgorithm) -> Result<&[u8]> {
        let index = if let Some(index) = self.digests.iter().position(|(existing, _)| *existing == algorithm) {
            index
        } else {
            let mut context = hash.new_hash(algorithm)?;
            for range in &self.ranges {
                context.update(&self.bytes[range.clone()])?;
            }
            let digest = context.finalize()?;
            if digest.len() != algorithm.digest_size() {
                return Err(CryptoError::Failed);
            }
            self.digests.push((algorithm, digest));
            self.digests.len() - 1
        };
        Ok(&self.digests[index].1)
    }

    pub(crate) fn signatures(&self) -> impl Iterator<Item = &'a [u8]> {
        let mut remaining = self.certificates;
        core::iter::from_fn(move || {
            while !remaining.is_empty() {
                let Ok((header, _)) = WinCertificateHeader::ref_from_prefix(remaining) else {
                    log::warn!("Truncated WIN_CERTIFICATE header");
                    remaining = &[];
                    return None;
                };
                let length = header.length.get() as usize;
                if length < size_of::<WinCertificateHeader>() {
                    log::warn!("Invalid WIN_CERTIFICATE length");
                    remaining = &[];
                    return None;
                }
                let Some(record) = remaining.get(..length) else {
                    log::warn!("Truncated WIN_CERTIFICATE payload");
                    remaining = &[];
                    return None;
                };
                let payload = &record[size_of::<WinCertificateHeader>()..];
                let padded = length.checked_add(7)? & !7;
                remaining = if padded >= remaining.len() { &[] } else { &remaining[padded..] };
                if header.revision.get() != 0x0200 {
                    continue;
                }
                match header.certificate_type.get() {
                    0x0002 => return Some(payload),
                    0x0ef1 => {
                        let Some((guid, signature)) = payload.split_first_chunk::<16>() else {
                            log::warn!("Truncated WIN_CERTIFICATE_UEFI_GUID");
                            continue;
                        };
                        if BinaryGuid::from_bytes(guid)
                            == BinaryGuid::from_string("4aafd29d-68df-49ee-8aa9-347d375665a7")
                        {
                            return Some(signature);
                        }
                    }
                    _ => {}
                }
            }
            None
        })
    }
}
