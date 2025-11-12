//! Module for a null section extractor that always returns Unsupported.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use alloc::vec::Vec;
use patina_ffs::{FirmwareFileSystemError, section::SectionExtractor};

pub struct NullSectionExtractor;

impl SectionExtractor for NullSectionExtractor {
    fn extract(&self, _: &patina_ffs::section::Section) -> Result<Vec<u8>, FirmwareFileSystemError> {
        Err(FirmwareFileSystemError::Unsupported)
    }
}