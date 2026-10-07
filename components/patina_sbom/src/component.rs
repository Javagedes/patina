//! SBOM ACPI table publisher component.
//!
//! ## License
//!
//! Copyright (C) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0

use alloc::boxed::Box;

use patina::{
    component::{
        component,
        params::{Commands, Config},
        service::{
            Service,
            uefi_services::{
                acpi::AcpiTableProtocol,
                event::{EventServices, EventServicesExt},
                tpl::{Tpl, TplServices},
            },
        },
    },
    error::Result,
    oem::OemInfo,
    uefi::event::READY_TO_BOOT_EVENT_GROUP_GUID,
};

use crate::service::SbomService;

/// Creates the SBOM collection service and publishes its ACPI table at Ready-to-Boot.
#[derive(Debug, Default)]
pub struct SbomComponent;

#[component]
impl SbomComponent {
    /// Creates an SBOM component.
    pub const fn new() -> Self {
        Self
    }

    fn entry_point(
        self,
        oem: Config<OemInfo>,
        events: Service<dyn EventServices>,
        acpi: AcpiTableProtocol,
        tpl: Service<dyn TplServices>,
        mut commands: Commands,
    ) -> Result<()> {
        let service: &'static SbomService = Box::leak(Box::new(SbomService::new(*oem, acpi, tpl)?));
        events.on_event_group(READY_TO_BOOT_EVENT_GROUP_GUID, Tpl::Callback, move || {
            if let Err(error) = service.publish() {
                log::error!("Failed to publish SBOM ACPI table at Ready-to-Boot: {error}");
            }
        })?;
        commands.add_service(service);
        Ok(())
    }
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
mod tests {
    extern crate std;

    use alloc::boxed::Box;
    use core::ffi::c_void;
    use std::{cell::RefCell, rc::Rc};

    use patina::{
        component::{
            params::{Commands, Config},
            service::uefi_services::{
                acpi::EfiAcpiTableProtocol,
                event::{Event, EventNotifyCallback, MockEventServices},
                protocol::{MockProtocolServices, ProtocolPtr},
                tpl::{MockTplServices, PreviousTpl, Tpl as ServiceTpl},
            },
        },
        protocol::ProtocolInterface,
        standard::efi,
    };

    use super::*;

    fn dummy_event() -> Event {
        Event::from_raw(core::ptr::NonNull::<core::ffi::c_void>::dangling().as_ptr())
            .expect("a dangling non-null pointer should produce a test event")
    }

    fn mock_tpl_services() -> MockTplServices {
        let mut tpl = MockTplServices::new();
        tpl.expect_raise_tpl().once().returning(|tpl| {
            assert_eq!(tpl, ServiceTpl::Notify);
            PreviousTpl::from_raw(4)
        });
        tpl.expect_restore_tpl().once().returning(|_| ());
        tpl
    }

    extern "efiapi" fn install_table(
        _protocol: *const EfiAcpiTableProtocol,
        table: *const c_void,
        table_size: usize,
        table_key: *mut usize,
    ) -> efi::Status {
        // SAFETY: The SBOM service passes a valid staging slice for the duration of this call.
        let table = unsafe { core::slice::from_raw_parts(table.cast::<u8>(), table_size) };
        assert_eq!(table.iter().copied().fold(0u8, u8::wrapping_add), 0);
        // SAFETY: The protocol contract requires a writable table-key pointer.
        unsafe { table_key.write(1) };
        efi::Status::SUCCESS
    }

    extern "efiapi" fn uninstall_table(_protocol: *const EfiAcpiTableProtocol, _table_key: usize) -> efi::Status {
        efi::Status::SUCCESS
    }

    fn mock_acpi_protocol() -> AcpiTableProtocol {
        let interface = Box::leak(Box::new(EfiAcpiTableProtocol::new(install_table, uninstall_table)));
        let interface = ProtocolPtr::from_raw(core::ptr::from_mut(interface).cast::<c_void>())
            .expect("protocol pointer is non-null");
        let mut protocols = MockProtocolServices::new();
        protocols.expect_locate_interface().once().returning_st(move |guid| {
            assert_eq!(guid, <EfiAcpiTableProtocol as ProtocolInterface>::PROTOCOL_GUID);
            Ok(interface)
        });
        AcpiTableProtocol::mock(Service::mock(Box::new(protocols)))
    }

    #[test]
    fn test_sbom_component_publishes_at_ready_to_boot() {
        let callback: Rc<RefCell<Option<EventNotifyCallback>>> = Rc::new(RefCell::new(None));
        let callback_for_mock = Rc::clone(&callback);
        let mut events = MockEventServices::new();
        events.expect_create_event_for_group().once().returning_st(move |group, tpl, event_callback| {
            assert_eq!(group, READY_TO_BOOT_EVENT_GROUP_GUID);
            assert_eq!(tpl, ServiceTpl::Callback);
            callback_for_mock.replace(Some(event_callback));
            Ok(dummy_event())
        });

        SbomComponent::new()
            .entry_point(
                Config::mock(OemInfo::new(*b"OEM_ID", *b"TABLE_ID", 1, 2, 3)),
                Service::mock(Box::new(events)),
                mock_acpi_protocol(),
                Service::mock(Box::new(mock_tpl_services())),
                Commands::mock(),
            )
            .expect("SBOM component should initialize");

        let mut callback = callback.borrow_mut().take().expect("Ready-to-Boot callback should be registered");
        callback(dummy_event());
    }
}
