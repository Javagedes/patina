//! Error types for cryptographic services.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use core::fmt;

use crate::error::EfiError;

/// Result type returned by cryptographic services.
pub type Result<T> = core::result::Result<T, CryptoError>;

/// Errors returned by cryptographic services.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CryptoError {
    /// An input was malformed, had an invalid length, or was otherwise rejected.
    InvalidParameter,
    /// The algorithm or operation is not supported by the crypto provider.
    Unsupported,
    /// The requested item was not present in the input.
    NotFound,
    /// A signature, certificate, or authentication tag failed verification.
    VerificationFailed,
    /// The provider could not allocate the resources required by the operation.
    OutOfResources,
    /// The provider reported a failure without a more specific reason.
    Failed,
}

impl fmt::Display for CryptoError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let message = match self {
            Self::InvalidParameter => "invalid parameter",
            Self::Unsupported => "unsupported operation",
            Self::NotFound => "not found",
            Self::VerificationFailed => "verification failed",
            Self::OutOfResources => "out of resources",
            Self::Failed => "operation failed",
        };
        f.write_str(message)
    }
}

impl core::error::Error for CryptoError {}

impl From<CryptoError> for EfiError {
    fn from(error: CryptoError) -> Self {
        match error {
            CryptoError::InvalidParameter => EfiError::InvalidParameter,
            CryptoError::Unsupported => EfiError::Unsupported,
            CryptoError::NotFound => EfiError::NotFound,
            CryptoError::VerificationFailed => EfiError::SecurityViolation,
            CryptoError::OutOfResources => EfiError::OutOfResources,
            CryptoError::Failed => EfiError::DeviceError,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::ToString;

    #[test]
    fn test_crypto_error_converts_to_efi_error() {
        let cases = [
            (CryptoError::InvalidParameter, EfiError::InvalidParameter),
            (CryptoError::Unsupported, EfiError::Unsupported),
            (CryptoError::NotFound, EfiError::NotFound),
            (CryptoError::VerificationFailed, EfiError::SecurityViolation),
            (CryptoError::OutOfResources, EfiError::OutOfResources),
            (CryptoError::Failed, EfiError::DeviceError),
        ];
        for (error, expected) in cases {
            assert_eq!(EfiError::from(error), expected);
        }
    }

    #[test]
    fn test_crypto_error_display() {
        assert_eq!(CryptoError::VerificationFailed.to_string(), "verification failed");
        assert_eq!(CryptoError::Failed.to_string(), "operation failed");
    }
}
