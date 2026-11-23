//! Native image-security handler registration.
//!
//! Handlers run before architectural security protocols during image loading.
//! All registered handlers must authorize an image; registration cannot override a denial.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use alloc::sync::Arc;

use crate::error::Result;

/// An image awaiting authentication, before mapping or relocation.
pub struct ImageAuthentication<'a> {
    /// Original file bytes, not the loaded image.
    pub image: &'a [u8],
    /// Whether the core obtained the image from an actual firmware volume.
    ///
    /// This classification must come from the loader, not merely a device-path node.
    pub from_firmware_volume: bool,
    /// Whether the caller requested boot-manager loading policy.
    pub boot_policy: bool,
}

/// A policy or measurement operation applied to an image before it is loaded.
///
/// Implementations must not retain borrowed image data. Handlers run at `TPL_APPLICATION`
/// and may be called recursively if their implementation loads another image.
pub trait ImageSecurityHandler: Send + Sync {
    /// Applies policy to the image.
    ///
    /// [`AccessDenied`](crate::error::EfiError::AccessDenied) prevents loading.
    /// [`SecurityViolation`](crate::error::EfiError::SecurityViolation) allows loading
    /// but prohibits starting the image, following the UEFI image-service semantics.
    fn authenticate(&self, request: &ImageAuthentication<'_>) -> Result<()>;
}

/// Registers additive image-security policies for the current boot.
///
/// Registration is permanent until the end of boot. A policy cannot remove another policy
/// or turn another handler's denial into authorization.
#[cfg_attr(any(test, feature = "mockall"), mockall::automock)]
pub trait SecurityServices {
    /// Registers a handler. Errors leave the registration unchanged.
    fn register_handler(&self, handler: Arc<dyn ImageSecurityHandler>) -> Result<()>;
}
