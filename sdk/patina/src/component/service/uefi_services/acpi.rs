//! ACPI Table Protocol component parameter.
//!
//! ## License
//!
//! Copyright (C) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0

use alloc::borrow::Cow;
use core::ffi::c_void;

use crate::{
    BinaryGuid,
    component::{
        MetaData, Storage, UnsafeStorageCell,
        params::Param,
        service::{
            Service,
            uefi_services::protocol::{ProtocolServices, ProtocolServicesExt},
        },
    },
    error::EfiError,
    protocol::ProtocolInterface,
    standard::efi,
};

/// Raw EFI ACPI table installation function.
#[doc(hidden)]
pub type AcpiTableInstall =
    extern "efiapi" fn(*const EfiAcpiTableProtocol, *const c_void, usize, *mut usize) -> efi::Status;
/// Raw EFI ACPI table removal function.
#[doc(hidden)]
pub type AcpiTableUninstall = extern "efiapi" fn(*const EfiAcpiTableProtocol, usize) -> efi::Status;

/// Raw `EFI_ACPI_TABLE_PROTOCOL` interface.
#[doc(hidden)]
#[repr(C)]
pub struct EfiAcpiTableProtocol {
    install_table: AcpiTableInstall,
    uninstall_table: AcpiTableUninstall,
}

impl EfiAcpiTableProtocol {
    /// Creates a raw ACPI Table Protocol interface.
    #[doc(hidden)]
    pub const fn new(install_table: AcpiTableInstall, uninstall_table: AcpiTableUninstall) -> Self {
        Self { install_table, uninstall_table }
    }
}

// SAFETY: `EfiAcpiTableProtocol` matches the C layout of `EFI_ACPI_TABLE_PROTOCOL`.
unsafe impl ProtocolInterface for EfiAcpiTableProtocol {
    const PROTOCOL_GUID: BinaryGuid = BinaryGuid::from_string("FFE06BDD-6107-46A6-7BB2-5A9C7EC5275C");
}

/// Provides direct access to the installed EFI ACPI Table Protocol.
///
/// Components can request this type directly in an entry point. Its [`Param`] implementation
/// depends on [`ProtocolServices`] and dispatches the component only after the protocol is present.
#[derive(Clone)]
pub struct AcpiTableProtocol {
    protocols: Service<dyn ProtocolServices>,
}

impl AcpiTableProtocol {
    /// Installs one complete ACPI table and returns its table key.
    ///
    /// # Errors
    ///
    /// Returns an error if the protocol is unavailable or rejects the table.
    pub fn install(&self, table: &[u8]) -> Result<usize, EfiError> {
        self.protocols
            .with_protocol::<EfiAcpiTableProtocol, _>(|protocol| {
                let mut table_key = 0;
                let status = (protocol.install_table)(
                    core::ptr::from_ref(protocol),
                    table.as_ptr().cast::<c_void>(),
                    table.len(),
                    &raw mut table_key,
                );
                EfiError::status_to_result(status).map(|()| table_key)
            })
            .map_err(EfiError::from)?
    }

    /// Uninstalls a table previously returned by [`Self::install`].
    ///
    /// # Errors
    ///
    /// Returns an error if the protocol is unavailable or rejects the table key.
    pub fn uninstall(&self, table_key: usize) -> Result<(), EfiError> {
        self.protocols
            .with_protocol::<EfiAcpiTableProtocol, _>(|protocol| {
                let status = (protocol.uninstall_table)(core::ptr::from_ref(protocol), table_key);
                EfiError::status_to_result(status)
            })
            .map_err(EfiError::from)?
    }

    /// Creates a protocol parameter backed by mocked protocol services.
    #[cfg(any(test, feature = "mockall"))]
    #[doc(hidden)]
    pub fn mock(protocols: Service<dyn ProtocolServices>) -> Self {
        Self { protocols }
    }
}

// SAFETY: This parameter delegates all Storage access tracking and retrieval to
// `Service<dyn ProtocolServices>`. Validation additionally verifies that the ACPI protocol is
// currently installed, and each operation re-locates it before dereferencing the interface.
unsafe impl Param for AcpiTableProtocol {
    type State = <Service<dyn ProtocolServices> as Param>::State;
    type Item<'storage, 'state> = Self;

    unsafe fn get_param<'storage, 'state>(
        state: &'state Self::State,
        storage: UnsafeStorageCell<'storage>,
    ) -> Self::Item<'storage, 'state> {
        // SAFETY: The component dispatcher calls this only after `validate` succeeds. Storage
        // access requirements are registered by the delegated Service parameter.
        let protocols = unsafe { <Service<dyn ProtocolServices> as Param>::get_param(state, storage) };
        Self { protocols }
    }

    fn validate(state: &Self::State, storage: UnsafeStorageCell) -> bool {
        if !<Service<dyn ProtocolServices> as Param>::validate(state, storage) {
            return false;
        }

        // SAFETY: The delegated Service parameter validated successfully above.
        let protocols = unsafe { <Service<dyn ProtocolServices> as Param>::get_param(state, storage) };
        protocols.locate_protocol::<EfiAcpiTableProtocol>().is_ok()
    }

    fn init_state(storage: &mut Storage, meta: &mut MetaData) -> Result<Self::State, Cow<'static, str>> {
        <Service<dyn ProtocolServices> as Param>::init_state(storage, meta)
    }
}
