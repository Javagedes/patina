//! SBOM entry collection service.
//!
//! ## License
//!
//! Copyright (C) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0

use alloc::vec::Vec;
use core::mem::{offset_of, size_of};

use patina::{
    acpi::{
        AcpiDescriptionHeader, EFI_ACPI_SBOM_TABLE_ENTRY_HEADER_LENGTH, EFI_ACPI_SBOM_TABLE_ENTRY_REVISION,
        EFI_ACPI_SBOM_TABLE_REVISION, EFI_ACPI_SBOM_TABLE_SIGNATURE, SbomTableEntryHeader,
    },
    component::service::{
        IntoService, Service,
        uefi_services::{acpi::AcpiTableProtocol, tpl::TplServices},
    },
    oem::OemInfo,
    uefi::{boot_services::tpl::Tpl, tpl_mutex::TplMutex},
};
use zerocopy::IntoBytes;

use crate::error::SbomError;

#[cfg(any(test, feature = "mockall"))]
use mockall::automock;

const ACPI_LENGTH_OFFSET: usize = offset_of!(AcpiDescriptionHeader, length);
const ACPI_CHECKSUM_OFFSET: usize = offset_of!(AcpiDescriptionHeader, checksum);

/// Collects SBOM payloads for publication in the SBOM ACPI table.
#[cfg_attr(any(test, feature = "mockall"), automock)]
pub trait Sbom {
    /// Adds one SBOM entry to the boot-time staging table.
    ///
    /// The payload is copied and may be released by the caller when this method returns.
    ///
    /// # Errors
    ///
    /// Returns [`SbomError`] if the table is busy, has already been published, cannot represent
    /// the requested size, or cannot grow its staging allocation.
    fn add_entry(&self, flags: u8, format: u8, compression: u8, payload: &[u8]) -> Result<(), SbomError>;
}

struct SbomState {
    table: Vec<u8>,
    published: bool,
}

impl SbomState {
    fn new(oem: OemInfo) -> Result<Self, SbomError> {
        let header = AcpiDescriptionHeader {
            signature: EFI_ACPI_SBOM_TABLE_SIGNATURE,
            length: u32::try_from(size_of::<AcpiDescriptionHeader>()).map_err(|_| SbomError::TableTooLarge)?,
            revision: EFI_ACPI_SBOM_TABLE_REVISION,
            checksum: 0,
            oem_id: oem.oem_id,
            oem_table_id: oem.oem_table_id,
            oem_revision: oem.oem_revision,
            creator_id: oem.creator_id,
            creator_revision: oem.creator_revision,
        };

        let mut table = Vec::new();
        table.try_reserve_exact(size_of::<AcpiDescriptionHeader>()).map_err(|_| SbomError::OutOfResources)?;
        table.extend_from_slice(header.as_bytes());
        Ok(Self { table, published: false })
    }

    fn add_entry(&mut self, flags: u8, format: u8, compression: u8, payload: &[u8]) -> Result<(), SbomError> {
        if self.published {
            return Err(SbomError::AlreadyPublished);
        }

        let payload_length = u32::try_from(payload.len()).map_err(|_| SbomError::PayloadTooLarge)?;
        let entry_size =
            size_of::<SbomTableEntryHeader>().checked_add(payload.len()).ok_or(SbomError::TableTooLarge)?;
        let table_size = self.table.len().checked_add(entry_size).ok_or(SbomError::TableTooLarge)?;
        let table_length = u32::try_from(table_size).map_err(|_| SbomError::TableTooLarge)?;

        self.table.try_reserve(entry_size).map_err(|_| SbomError::OutOfResources)?;
        let header = SbomTableEntryHeader {
            revision: EFI_ACPI_SBOM_TABLE_ENTRY_REVISION,
            header_length: EFI_ACPI_SBOM_TABLE_ENTRY_HEADER_LENGTH,
            payload_length,
            flags,
            format,
            compression,
        };
        self.table.extend_from_slice(header.as_bytes());
        self.table.extend_from_slice(payload);
        self.table
            .get_mut(ACPI_LENGTH_OFFSET..ACPI_LENGTH_OFFSET + size_of::<u32>())
            .expect("SBOM staging table always contains a complete ACPI header")
            .copy_from_slice(&table_length.to_ne_bytes());
        *self.table.get_mut(ACPI_CHECKSUM_OFFSET).expect("SBOM staging table always contains a complete ACPI header") =
            0;
        Ok(())
    }

    fn finalize(&mut self) {
        *self.table.get_mut(ACPI_CHECKSUM_OFFSET).expect("SBOM staging table always contains a complete ACPI header") =
            0;
        let sum = self.table.iter().copied().fold(0u8, u8::wrapping_add);
        *self.table.get_mut(ACPI_CHECKSUM_OFFSET).expect("SBOM staging table always contains a complete ACPI header") =
            0u8.wrapping_sub(sum);
    }
}

/// TPL-safe implementation of the [`Sbom`] collection service.
#[derive(IntoService)]
#[service(dyn Sbom)]
pub(crate) struct SbomService {
    state: TplMutex<SbomState, Service<dyn TplServices>>,
    acpi: AcpiTableProtocol,
}

impl SbomService {
    pub(crate) fn new(oem: OemInfo, acpi: AcpiTableProtocol, tpl: Service<dyn TplServices>) -> Result<Self, SbomError> {
        Ok(Self { state: TplMutex::new(tpl, Tpl::NOTIFY, SbomState::new(oem)?), acpi })
    }

    pub(crate) fn publish(&self) -> Result<(), SbomError> {
        let mut state = self.state.try_lock().map_err(|()| SbomError::Busy)?;
        if state.published {
            return Ok(());
        }

        state.finalize();
        self.acpi.install(&state.table).map_err(SbomError::PublishFailed)?;
        state.published = true;
        Ok(())
    }
}

impl Sbom for SbomService {
    fn add_entry(&self, flags: u8, format: u8, compression: u8, payload: &[u8]) -> Result<(), SbomError> {
        self.state.try_lock().map_err(|()| SbomError::Busy)?.add_entry(flags, format, compression, payload)
    }
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
mod tests {
    extern crate std;

    use alloc::boxed::Box;
    use core::ffi::c_void;
    use std::sync::atomic::{AtomicUsize, Ordering};

    use patina::{
        acpi::{
            EFI_ACPI_SBOM_TABLE_ENTRY_FLAG_NONE, EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_COMPRESSION_NONE,
            EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_FORMAT_SPDX, SbomTable,
        },
        component::service::uefi_services::{
            acpi::EfiAcpiTableProtocol,
            protocol::{MockProtocolServices, ProtocolPtr},
            tpl::{MockTplServices, PreviousTpl, Tpl as ServiceTpl},
        },
        error::EfiError,
        protocol::ProtocolInterface,
        standard::efi,
    };

    use super::*;

    static INSTALL_ATTEMPTS: AtomicUsize = AtomicUsize::new(0);

    fn oem_info() -> OemInfo {
        OemInfo::new(*b"OEM_ID", *b"TABLE_ID", 1, 2, 3)
    }

    fn mock_tpl_services(lock_count: usize) -> MockTplServices {
        let mut tpl = MockTplServices::new();
        tpl.expect_raise_tpl()
            .times(lock_count)
            .withf(|tpl| *tpl == ServiceTpl::Notify)
            .returning(|_| PreviousTpl::from_raw(4));
        tpl.expect_restore_tpl().times(lock_count).returning(|_| ());
        tpl
    }

    extern "efiapi" fn install_success(
        _protocol: *const EfiAcpiTableProtocol,
        table: *const c_void,
        table_size: usize,
        table_key: *mut usize,
    ) -> efi::Status {
        // SAFETY: The SBOM service passes a valid staging slice for the duration of this call.
        let table_bytes = unsafe { core::slice::from_raw_parts(table.cast::<u8>(), table_size) };
        assert_eq!(table_bytes.iter().copied().fold(0u8, u8::wrapping_add), 0);

        let (table, remaining) = SbomTable::parse_prefix(table_bytes).expect("published table should parse");
        assert!(remaining.is_empty());
        let oem_id = table.header.oem_id;
        let oem_table_id = table.header.oem_table_id;
        assert_eq!(oem_id, *b"OEM_ID");
        assert_eq!(oem_table_id, *b"TABLE_ID");

        let mut entries = table.entries().expect("published entries should validate");
        let entry = entries.next().expect("published entry should exist");
        assert_eq!(entry.payload(), &[0x11, 0x22, 0x33]);
        assert!(entries.next().is_none());

        // SAFETY: The protocol contract requires a writable table-key pointer.
        unsafe { table_key.write(1) };
        efi::Status::SUCCESS
    }

    extern "efiapi" fn install_fails_once(
        _protocol: *const EfiAcpiTableProtocol,
        _table: *const c_void,
        _table_size: usize,
        table_key: *mut usize,
    ) -> efi::Status {
        if INSTALL_ATTEMPTS.fetch_add(1, Ordering::Relaxed) == 0 {
            efi::Status::OUT_OF_RESOURCES
        } else {
            // SAFETY: The protocol contract requires a writable table-key pointer.
            unsafe { table_key.write(1) };
            efi::Status::SUCCESS
        }
    }

    extern "efiapi" fn uninstall_success(_protocol: *const EfiAcpiTableProtocol, _table_key: usize) -> efi::Status {
        efi::Status::SUCCESS
    }

    fn mock_acpi_protocol(
        install: patina::component::service::uefi_services::acpi::AcpiTableInstall,
        locate_count: usize,
    ) -> AcpiTableProtocol {
        let interface = Box::leak(Box::new(EfiAcpiTableProtocol::new(install, uninstall_success)));
        let interface = ProtocolPtr::from_raw(core::ptr::from_mut(interface).cast::<c_void>())
            .expect("protocol pointer is non-null");
        let mut protocols = MockProtocolServices::new();
        protocols.expect_locate_interface().times(locate_count).returning_st(move |guid| {
            assert_eq!(guid, <EfiAcpiTableProtocol as ProtocolInterface>::PROTOCOL_GUID);
            Ok(interface)
        });
        AcpiTableProtocol::mock(Service::mock(Box::new(protocols)))
    }

    #[test]
    fn test_sbom_service_adds_entry_and_publishes_checksumming_table() {
        let service = SbomService::new(
            oem_info(),
            mock_acpi_protocol(install_success, 1),
            Service::mock(Box::new(mock_tpl_services(4))),
        )
        .expect("SBOM service should initialize");
        let mut payload = [0x11, 0x22, 0x33];

        service
            .add_entry(
                EFI_ACPI_SBOM_TABLE_ENTRY_FLAG_NONE,
                EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_FORMAT_SPDX,
                EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_COMPRESSION_NONE,
                &payload,
            )
            .expect("SBOM entry should be added");
        payload.fill(0);

        service.publish().expect("SBOM table should publish");
        service.publish().expect("repeated publication should be idempotent");
        assert_eq!(
            service.add_entry(
                EFI_ACPI_SBOM_TABLE_ENTRY_FLAG_NONE,
                EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_FORMAT_SPDX,
                EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_COMPRESSION_NONE,
                &[]
            ),
            Err(SbomError::AlreadyPublished)
        );
    }

    #[test]
    fn test_sbom_service_retries_after_acpi_publication_failure() {
        INSTALL_ATTEMPTS.store(0, Ordering::Relaxed);

        let service = SbomService::new(
            oem_info(),
            mock_acpi_protocol(install_fails_once, 2),
            Service::mock(Box::new(mock_tpl_services(3))),
        )
        .expect("SBOM service should initialize");

        assert_eq!(service.publish(), Err(SbomError::PublishFailed(EfiError::OutOfResources)));
        service.publish().expect("second publication attempt should succeed");
        service.publish().expect("publication should then be idempotent");
        assert_eq!(INSTALL_ATTEMPTS.load(Ordering::Relaxed), 2);
    }
}
