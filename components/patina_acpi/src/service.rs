//! ACPI Service Definitions.
//!
//! Defines the ACPI Provider for use as a service.
//!
//! ## License
//!
//! Copyright (C) Microsoft Corporation. All rights reserved.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use core::ops::Deref;

use alloc::vec::Vec;
use patina::component::service::Service;
use r_efi::efi;

use crate::{acpi_table::AcpiTableHeader, error::AcpiError};

// Re-export all table structs as they are part of the service API
pub use crate::table::*;

#[cfg(any(test, feature = "mockall"))]
use mockall::automock;

/// Represents an opaque reference to an installed ACPI table.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TableKey(pub(crate) usize);

/// A notification function that is called when a new ACPI table is installed.
pub type AcpiNotifyFn = fn(
    &AcpiTableHeader, /* Standard ACPI header. */
    u32,              /* Supported ACPI versions. */
    usize,            /* Table key. */
) -> efi::Status;

/// TODO
#[cfg_attr(any(test, feature = "mockall"), automock)]
pub trait Acpi {
    /// Installs the bytes as an ACPI table
    ///
    /// Returns a key usable with [Acpi::get_table].
    ///
    /// ## Safety
    ///
    /// - The bytes must represent a valid ACPI Table. A valid ACPI Table meets the same safety requirements as
    ///   required for the [AcpiTable] trait.
    unsafe fn install_table(&self, table: &[u8]) -> Result<TableKey, AcpiError>;

    /// Gets a table by its key.
    ///
    /// ## Errors
    ///
    /// Returns [AcpiError::NotFound] if the table is not found.
    /// Returns [AcpiError::InvalidLength] if the table is not long enough for an [AcpiTableHeader].
    fn get_table(&self, key: &TableKey) -> Result<Vec<u8>, AcpiError>;

    /// Removes a table and returns it to the caller
    ///
    /// ## Errors
    ///
    /// Returns [AcpiError::NotFound] if the table is not found.
    /// Returns [AcpiError::InvalidLength] if the table is not long enough for an [AcpiTableHeader].
    fn uninstall_table(&self, key: TableKey) -> Result<Vec<u8>, AcpiError>;

    /// Registers a function that will be called whenever a new ACPI table is installed.
    fn register_notify(&self, notify_fn: AcpiNotifyFn) -> Result<(), AcpiError>;

    /// Unregisters a function that will be called whenever a new ACPI table is installed.
    ///
    /// ## Errors
    ///
    /// Returns [AcpiError::InvalidNotifyUnregister] if the notify fn was not found.
    fn unregister_notify(&self, notify_fn: AcpiNotifyFn) -> Result<(), AcpiError>;

    /// Returns a copy of all registered ACPI tables.
    fn collect_tables(&self) -> Vec<Vec<u8>>;
}

/// An extension trait to provide generic methods for convenience
pub trait AcpiExt {
    /// Installs the ACPI Table
    ///
    /// Returns a key usable with [Acpi::get_table].
    ///
    fn install_table<T: AcpiTable>(&self, table: &T) -> Result<TableKey, AcpiError>;

    /// Gets a table by its key.
    ///
    /// ## Errors
    ///
    /// Returns [AcpiError::NotFound] if the table is not found
    /// Returns [AcpiError::InvalidSignature] if the table signature does not match [T::SIGNATURE]
    /// Returns [AcpiError::BadFormat] if the conversion to `T` failed.
    fn get_table<T: AcpiTable>(&self, key: &TableKey) -> Result<Table<T>, AcpiError>;

    /// A convenience method to uninstall a table, edit it, and re-install the table
    ///
    /// ## Errors
    ///
    /// Returns [AcpiError::NotFound] if the table is not found
    /// Returns [AcpiError::InvalidSignature] if the table signature does not match T::SIGNATURE
    /// Returns [AcpiError::BadFormat] if the conversion to `T` failed.
    #[must_use = "The closure is not called if this function returns an error"]
    fn mutate_table<F, T>(&self, key: &TableKey, f: F) -> Result<(), AcpiError>
    where
        T: AcpiTable,
        F: FnOnce(&mut Table<T>) -> Result<(), AcpiError>;
}

/// This is a way to have generic methods on a service interface, by implementing the generics on the
/// service itself.
impl AcpiExt for Service<dyn Acpi> {
    fn install_table<T: AcpiTable>(&self, table: &T) -> Result<TableKey, AcpiError> {
        // SAFETY: The safety requirements for `AcpiTable` ensure that the table starts with a valid ACPI header.
        unsafe { self.deref().install_table(table.as_bytes()) }
    }

    fn get_table<T: AcpiTable>(&self, key: &TableKey) -> Result<Table<T>, AcpiError> {
        let bytes = self.deref().get_table(key)?;
        Table::<T>::try_from(bytes)
    }

    fn mutate_table<F, T>(&self, _key: &TableKey, _f: F) -> Result<(), AcpiError>
    where
        T: AcpiTable,
        F: FnOnce(&mut Table<T>) -> Result<(), AcpiError>,
    {
        todo!()
    }
}
