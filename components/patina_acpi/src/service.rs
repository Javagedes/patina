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
use core::any::TypeId;

use alloc::vec::Vec;
use patina::component::service::{IntoService, Service, memory::MemoryManager};
use r_efi::efi;

use crate::{
    acpi_table::{AcpiTableHeader, Table},
    error::AcpiError,
};

use zerocopy::*;

#[cfg(any(test, feature = "mockall"))]
use mockall::automock;

/// A trait to allow treating a type as an ACPI table.
///
/// This trait relies on [zerocopy] traits to safely convert between byte slices and the ACPI table struct.
/// Satisfying the trait requirements for [zerocopy::FromBytes], [zerocopy::IntoBytes], [zerocopy::Immutable],
/// and [zerocopy::KnownLayout] ensures that the type can be safely converted to and from byte slices without
/// violating memory safety.
///
/// # Safety
///
/// - Implementors of this trait must ensure that the first field of the struct is an [AcpiTableHeader].
pub unsafe trait AcpiTable: FromBytes + IntoBytes + Immutable + KnownLayout {
    fn header(&self) -> &AcpiTableHeader {
        // SAFETY: This is safe as long as the first field of any struct implementing AcpiTable is an AcpiTableHeader.
        <AcpiTableHeader as zerocopy::FromBytes>::ref_from_prefix(self.as_bytes()).expect("").0
    }
}
/// Represents an opaque reference to an installed ACPI table.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TableKey(pub(crate) usize);

/// A notification function that is called when a new ACPI table is installed.
pub type AcpiNotifyFn = fn(
    &AcpiTableHeader, /* Standard ACPI header. */
    u32,              /* Supported ACPI versions. */
    usize,            /* Table key. */
) -> efi::Status;

/// The `AcpiTableManager` provides an interface for installing, uninstalling, and accessing ACPI tables.
/// This struct serves as the API by which external components can access ACPI services.
#[derive(IntoService)]
#[service(AcpiTableManager)]
pub struct AcpiTableManager {
    pub(crate) provider_service: Service<dyn AcpiProvider>,
    pub(crate) memory_manager: Service<dyn MemoryManager>,
}

impl AcpiTableManager {
    /// Installs an ACPI table.
    ///
    /// `table` should point to an ACPI table with a standard ACPI header, followed by any additional trailing bytes specific to the table.
    /// The `length` field of the `AcpiTableHeader` must be set to the total size of the table, including the header and any trailing bytes.
    ///
    /// The table, unless it is the FACS or DSDT, will be added to the list of installed tables in the XSDT.
    /// (The FACS and DSDT are accessible only through fields in the FADT.)
    ///
    /// CAUTION: This implementation of ACPI prevents duplicate installations of the XSDT, FADT, FACS, and DSDT.
    /// Attempts to install a duplicate of the listed tables will result in a failed installation.
    ///
    /// The returned `TableKey` can be used to uninstall the table later.
    /// It is an opaque reference to the table and should not be manipulated directly.
    pub fn install_acpi_table<T: AcpiTable + 'static>(&self, table: T) -> Result<TableKey, AcpiError> {
        let acpi_table = Table::new(table, &self.memory_manager)?;
        self.provider_service.install_acpi_table(acpi_table)
    }

    /// Uninstalls an ACPI table.
    ///
    /// The `table_key` is the opaque reference returned by `install_acpi_table`.
    ///
    /// This function will remove the table from the XSDT and free the memory associated with it.
    pub fn uninstall_acpi_table(&self, table_key: TableKey) -> Result<(), AcpiError> {
        self.provider_service.uninstall_acpi_table(table_key)
    }

    /// Retrieves an ACPI table by its table key.
    ///
    /// The `table_key` is the opaque reference returned by `install_acpi_table`.
    ///
    /// The generic type `T` should be the expected type of the table, which should match the type passed in during installation.
    /// To cast retrieved tables to different types, or to retrieve tables across the C FFI protocol interface,
    /// use `get_acpi_table_unchecked` for a untyped retrieval.
    ///
    /// The RSDP and XSDT cannot be accessed through `get_acpi_table`.
    pub fn get_acpi_table<T: AcpiTable + 'static>(&self, table_key: TableKey) -> Result<&T, AcpiError> {
        let acpi_table = self.provider_service.get_acpi_table(table_key)?;

        // There may be ACPI tables whose type is unknown at installation, due to installation from the HOB or a C protocol.
        // In these cases, the type is is unspecified (AcpiTableHeader instead of a specific table type), so we skip type checking.
        // In all other cases, verify the type provided by the user is valid.
        if acpi_table.type_id != TypeId::of::<T>() {
            return Err(AcpiError::InvalidTableType);
        }

        Ok(acpi_table.as_ref().unwrap())
    }

    /// Retrieves an ACPI table by its table key.
    ///
    /// The `table_key` is the opaque reference returned by `install_acpi_table`.
    ///
    /// When using `get_acpi_table_unchecked`, no type checking occurs on the retrieved table.
    /// This function should be used to cast tables to a different type from their installation type,
    /// or to retrieve tables across the C FFI protocol interface.
    ///
    /// The RSDP and XSDT cannot be accessed through `get_acpi_table_unchecked`.
    ///
    /// ## SAFETY
    ///
    /// - The caller must ensure the type T is a valid representation for the retrieved table.
    pub unsafe fn get_acpi_table_unchecked<T: 'static>(&self, table_key: TableKey) -> Result<&T, AcpiError> {
        let acpi_table = self.provider_service.get_acpi_table(table_key)?;

        // Cast the table to its expected type.
        let raw_table_ptr: *const T = acpi_table.as_ptr() as *const T;

        // SAFETY: The installed tables are stored in the provider and live at least as long as `self`.
        Ok(unsafe { &*raw_table_ptr })
    }

    /// Registers a function which will be called whenever a new ACPI table is installed.
    pub fn register_notify(&self, notify_fn: AcpiNotifyFn) -> Result<(), AcpiError> {
        self.provider_service.register_notify(true, notify_fn)
    }

    /// Unregisters an existing notification function.
    /// The function must have been previously registered with `register_notify`.
    pub fn unregister_notify(&self, notify_fn: AcpiNotifyFn) -> Result<(), AcpiError> {
        self.provider_service.register_notify(false, notify_fn)
    }

    /// Returns an iterator over the installed ACPI tables.
    /// Each returned `AcpiTableHeader` points to the header of an ACPI table installed in ACPI memory.
    ///
    /// This can be used in place of `get_acpi_table`, or in conjunction with it to retrieve a specific table reference.
    ///
    /// The RSDP and XSDT are not included in the list of iterable ACPI tables.
    pub fn iter_tables(&self) -> Vec<&Table> {
        self.provider_service.collect_tables()
    }
}

/// The `AcpiTableManager` provides functionality for installing, uninstalling, and accessing ACPI tables.
/// This struct serves as the API by which internal implementations can provide custom ACPI implementation.
#[cfg_attr(any(test, feature = "mockall"), automock)]
#[allow(clippy::needless_lifetimes)] // Lifetimes necessary to satisfy mockall.
pub(crate) trait AcpiProvider {
    /// Installs an ACPI table and returns an associated key which can be used to get or uninstall the table later.
    fn install_acpi_table(&self, acpi_table: Table) -> Result<TableKey, AcpiError>;

    /// Uninstalls an ACPI table using the same `table_key` returned at the time of installation.
    fn uninstall_acpi_table(&self, table_key: TableKey) -> Result<(), AcpiError>;

    /// Retrieves an ACPI table by its table key. This must be the same key returned at the time of installation.
    fn get_acpi_table<'a>(&'a self, table_key: TableKey) -> Result<&'a Table, AcpiError>;

    /// Registers or unregisters a function which will be called whenever a new ACPI table is installed.
    fn register_notify(&self, should_register: bool, notify_fn: AcpiNotifyFn) -> Result<(), AcpiError>;

    /// Returns all currently installed tables in an iterable format.
    fn collect_tables<'a>(&'a self) -> Vec<&'a Table>;
}

#[cfg(test)]
#[coverage(off)]
mod tests {
    use alloc::boxed::Box;
    use core::mem;
    use patina::component::service::memory::StdMemoryManager;

    use crate::acpi_table::AcpiFadt;

    use super::*;

    #[test]
    fn test_get_table_wrong_type() {
        // // Allow Send and Sync for AcpiTable in this test context.
        // #[allow(non_local_definitions)]
        // // SAFETY: This is only for testing purposes.
        // unsafe impl Send for AcpiTable {}
        // #[allow(non_local_definitions)]
        // // SAFETY: This is only for testing purposes.
        // unsafe impl Sync for AcpiTable {}

        // SAFETY: The constructed table is a valid ACPI table.
        fn table() -> &'static Table {
            let table = Table::new(
                AcpiFadt {
                    header: AcpiTableHeader { length: mem::size_of::<AcpiFadt>() as u32, ..Default::default() },
                    ..Default::default()
                },
                &Service::mock(Box::new(StdMemoryManager::new())),
            )
            .unwrap();
            Box::leak(Box::new(table))
        }

        let mut mock_acpi_provider = MockAcpiProvider::new();
        mock_acpi_provider.expect_get_acpi_table().returning(move |_table_key| Ok(table()));
        let provider = AcpiTableManager {
            provider_service: Service::mock(Box::new(mock_acpi_provider)),
            memory_manager: Service::mock(Box::new(StdMemoryManager::new())),
        };

        // SAFETY: TODO
        unsafe impl AcpiTable for TestTable {}

        #[derive(Clone, Copy, Debug, PartialEq, Eq, IntoBytes, FromBytes, Immutable, KnownLayout)]
        struct TestTable;

        let result = provider.get_acpi_table::<TestTable>(TableKey(0));
        assert_eq!(result, Err(AcpiError::InvalidTableType));
    }
}
