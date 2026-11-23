//! Component registering Secure Boot image verification.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use crate::{
    measurement::{AuthorityMeasurement, DATABASE_GUID},
    verification,
};
use alloc::{sync::Arc, vec::Vec};
use patina::{
    BinaryGuid, char16,
    component::{
        component,
        service::{
            Service,
            security::{ImageAuthentication, ImageSecurityHandler, SecurityServices},
            uefi_services::{protocol::ProtocolServices, tpl::TplServices},
        },
    },
    crypto::{hash::Hash, signature::Signature},
    error::{EfiError, Result},
    standard::efi,
    uefi::runtime_services::{RuntimeServices, StandardRuntimeServices},
};

/// Registers image authorization using `db`, `dbx`, and the SDK crypto services.
///
/// Firmware-volume images bypass verification. Other images are checked when the
/// `SecureBoot` variable equals one. Missing SecureBoot means disabled; malformed values
/// and variable-service failures deny loading. Existing architectural security policies
/// still run after this handler and may also deny an image.
#[derive(Debug, Default, Clone, Copy)]
pub struct SecureBootComponent;

#[component]
impl SecureBootComponent {
    /// Creates the Secure Boot component.
    pub const fn new() -> Self {
        Self
    }

    fn entry_point(
        self,
        security: Service<dyn SecurityServices>,
        hash: Service<dyn Hash>,
        signature: Service<dyn Signature>,
        protocols: Service<dyn ProtocolServices>,
        tpl: Service<dyn TplServices>,
        runtime: StandardRuntimeServices,
    ) -> Result<()> {
        security.register_handler(Arc::new(SecureBootHandler {
            hash,
            signature,
            runtime,
            measurement: AuthorityMeasurement::new(protocols, tpl),
        }))?;
        log::info!("Secure Boot image-security handler registered");
        Ok(())
    }
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
#[path = "component_tests.rs"]
mod tests;

struct SecureBootHandler<R = StandardRuntimeServices> {
    hash: Service<dyn Hash>,
    signature: Service<dyn Signature>,
    runtime: R,
    measurement: AuthorityMeasurement,
}

impl<R: RuntimeServices> SecureBootHandler<R> {
    fn variable(&self, name: &patina::Char16Str, namespace: BinaryGuid) -> Result<Option<Vec<u8>>> {
        match self.runtime.get_variable::<Vec<u8>>(name, &namespace.into_inner(), None) {
            Ok((data, _)) => Ok(Some(data)),
            Err(efi::Status::NOT_FOUND) => Ok(None),
            Err(status) => {
                log::error!("Unable to read Secure Boot variable {name:?}: {status:?}");
                Err(EfiError::AccessDenied)
            }
        }
    }
}

impl<R: RuntimeServices + Send + Sync> ImageSecurityHandler for SecureBootHandler<R> {
    fn authenticate(&self, request: &ImageAuthentication<'_>) -> Result<()> {
        if request.from_firmware_volume {
            return Ok(());
        }
        let global = BinaryGuid::from_string("8be4df61-93ca-11d2-aa0d-00e098032b8c");
        let enabled = self.variable(char16!("SecureBoot"), global)?;
        match enabled.as_deref() {
            None | Some([0]) => return Ok(()),
            Some([1]) => {}
            _ => {
                log::error!("Malformed SecureBoot variable");
                return Err(EfiError::AccessDenied);
            }
        }
        let db = self.variable(char16!("db"), DATABASE_GUID)?.unwrap_or_default();
        let dbx = self.variable(char16!("dbx"), DATABASE_GUID)?.unwrap_or_default();
        let authority =
            verification::verify(request.image, &db, &dbx, *self.hash, *self.signature).map_err(|error| {
                log::warn!("Secure Boot image authorization failed: {error}");
                EfiError::AccessDenied
            })?;
        if let Some(authority) = authority
            && let Err(error) = self.measurement.measure(&authority)
        {
            // Measurement failures do not change authorization, matching SecureBootHook.
            log::warn!("Unable to measure Secure Boot authority into PCR 7: {error:?}");
        }
        Ok(())
    }
}
