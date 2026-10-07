//! SBOM service errors.
//!
//! ## License
//!
//! Copyright (C) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0

use core::fmt;

use patina::error::EfiError;

/// Errors returned while collecting or publishing SBOM data.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SbomError {
    /// The SBOM service is currently being accessed by another callback.
    Busy,
    /// The SBOM table has already been published and can no longer be modified.
    AlreadyPublished,
    /// The payload length cannot be represented in the SBOM entry format.
    PayloadTooLarge,
    /// The complete table length cannot be represented in the ACPI header.
    TableTooLarge,
    /// The staging buffer could not be grown.
    OutOfResources,
    /// The completed table could not be installed by the ACPI service.
    PublishFailed(EfiError),
}

impl fmt::Display for SbomError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Busy => f.write_str("SBOM service is busy"),
            Self::AlreadyPublished => f.write_str("SBOM table has already been published"),
            Self::PayloadTooLarge => f.write_str("SBOM payload is too large"),
            Self::TableTooLarge => f.write_str("SBOM ACPI table is too large"),
            Self::OutOfResources => f.write_str("SBOM staging allocation failed"),
            Self::PublishFailed(error) => write!(f, "SBOM ACPI table publication failed: {error}"),
        }
    }
}

impl core::error::Error for SbomError {}

impl From<SbomError> for EfiError {
    fn from(error: SbomError) -> Self {
        match error {
            SbomError::Busy => Self::NotReady,
            SbomError::AlreadyPublished => Self::AlreadyStarted,
            SbomError::PayloadTooLarge | SbomError::TableTooLarge => Self::BadBufferSize,
            SbomError::OutOfResources => Self::OutOfResources,
            SbomError::PublishFailed(error) => error,
        }
    }
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
mod tests {
    extern crate alloc;

    use alloc::format;

    use super::*;

    #[test]
    fn test_sbom_error_converts_to_efi_error() {
        assert_eq!(EfiError::from(SbomError::Busy), EfiError::NotReady);
        assert_eq!(EfiError::from(SbomError::AlreadyPublished), EfiError::AlreadyStarted);
        assert_eq!(EfiError::from(SbomError::PayloadTooLarge), EfiError::BadBufferSize);
        assert_eq!(EfiError::from(SbomError::TableTooLarge), EfiError::BadBufferSize);
        assert_eq!(EfiError::from(SbomError::OutOfResources), EfiError::OutOfResources);
        assert_eq!(EfiError::from(SbomError::PublishFailed(EfiError::DeviceError)), EfiError::DeviceError);
    }

    #[test]
    fn test_sbom_error_display() {
        assert_eq!(format!("{}", SbomError::Busy), "SBOM service is busy");
        assert_eq!(format!("{}", SbomError::AlreadyPublished), "SBOM table has already been published");
        assert_eq!(format!("{}", SbomError::PayloadTooLarge), "SBOM payload is too large");
        assert_eq!(format!("{}", SbomError::TableTooLarge), "SBOM ACPI table is too large");
        assert_eq!(format!("{}", SbomError::OutOfResources), "SBOM staging allocation failed");
        assert_eq!(
            format!("{}", SbomError::PublishFailed(EfiError::DeviceError)),
            "SBOM ACPI table publication failed: Device Error"
        );
    }
}
