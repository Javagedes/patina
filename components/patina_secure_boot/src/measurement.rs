//! PCR 7 authority events through the TCG2 protocol.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use alloc::vec::Vec;
use patina::{
    BinaryGuid,
    component::service::{
        Service,
        uefi_services::{
            protocol::{ProtocolError, ProtocolServices, ProtocolServicesExt},
            tpl::TplServices,
        },
    },
    error::{EfiError, Result},
    protocol::ProtocolInterface,
    standard::efi,
    uefi::{boot_services::tpl::Tpl, tpl_mutex::TplMutex},
};

pub(crate) const DATABASE_GUID: BinaryGuid = BinaryGuid::from_string("d719b2cb-3d3a-4596-a3bc-dad00e67656f");
const VARIABLE_AUTHORITY: u32 = 0x8000_00e0;

#[repr(C)]
struct Tcg2Protocol {
    get_capability: usize,
    get_event_log: usize,
    hash_log_extend_event: extern "efiapi" fn(*const Self, u64, u64, u64, *const u8) -> efi::Status,
    submit_command: usize,
    get_active_pcr_banks: usize,
    set_active_pcr_banks: usize,
    get_result_of_set_active_pcr_banks: usize,
}

// SAFETY: This repr(C) layout follows EFI_TCG2_PROTOCOL, including all seven function slots.
unsafe impl ProtocolInterface for Tcg2Protocol {
    const PROTOCOL_GUID: BinaryGuid = BinaryGuid::from_string("607f766c-7455-42be-930b-e4d76db2720f");
}

pub(crate) struct AuthorityMeasurement {
    protocols: Service<dyn ProtocolServices>,
    measured: TplMutex<Vec<Vec<u8>>, Service<dyn TplServices>>,
}

impl AuthorityMeasurement {
    pub(crate) fn new(protocols: Service<dyn ProtocolServices>, tpl: Service<dyn TplServices>) -> Self {
        Self { protocols, measured: TplMutex::new(tpl, Tpl::NOTIFY, Vec::new()) }
    }

    pub(crate) fn measure(&self, authority: &[u8]) -> Result<()> {
        {
            let mut measured = self.measured.checked_lock()?;
            if measured.iter().any(|existing| existing == authority) {
                return Ok(());
            }
            // Reserve the authority before calling firmware, which can re-enter image loading.
            measured.push(authority.to_vec());
        }
        let result = self.extend(authority);
        if result.is_err() {
            // A stale reservation could make a later failed measurement appear successful.
            self.measured
                .checked_lock()
                .expect("failed measurement reservation must be removed")
                .retain(|existing| existing != authority);
        }
        result
    }

    fn extend(&self, authority: &[u8]) -> Result<()> {
        let tcg2 = self.protocols.locate_protocol::<Tcg2Protocol>().map_err(|error| match error {
            ProtocolError::NotFound => EfiError::NotFound,
            _ => EfiError::DeviceError,
        })?;
        let data = authority_event_data(authority);
        let event = tcg_event(&data)?;
        EfiError::status_to_result((tcg2.hash_log_extend_event)(
            tcg2,
            0,
            data.as_ptr() as usize as u64,
            data.len() as u64,
            event.as_ptr(),
        ))
    }
}

fn authority_event_data(authority: &[u8]) -> Vec<u8> {
    let mut data = Vec::new();
    data.extend_from_slice(DATABASE_GUID.as_bytes());
    data.extend_from_slice(&2u64.to_le_bytes());
    data.extend_from_slice(&(authority.len() as u64).to_le_bytes());
    data.extend_from_slice(&[b'd', 0, b'b', 0]);
    data.extend_from_slice(authority);
    data
}

fn tcg_event(data: &[u8]) -> Result<Vec<u8>> {
    // EFI_TCG2_EVENT and its header are packed, with an 18-byte fixed portion.
    let size = data.len().checked_add(18).and_then(|size| u32::try_from(size).ok()).ok_or(EfiError::OutOfResources)?;
    let mut event = Vec::new();
    event.extend_from_slice(&size.to_le_bytes());
    event.extend_from_slice(&14u32.to_le_bytes());
    event.extend_from_slice(&1u16.to_le_bytes());
    event.extend_from_slice(&7u32.to_le_bytes());
    event.extend_from_slice(&VARIABLE_AUTHORITY.to_le_bytes());
    event.extend_from_slice(data);
    Ok(event)
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
pub(crate) mod tests {
    use super::*;
    use alloc::boxed::Box;
    use patina::component::service::uefi_services::{
        protocol::{MockProtocolServices, ProtocolPtr},
        tpl::{MockTplServices, PreviousTpl},
    };

    pub(crate) fn tpl() -> Service<dyn TplServices> {
        let mut tpl = MockTplServices::new();
        tpl.expect_raise_tpl().returning(|_| PreviousTpl::from_raw(4));
        tpl.expect_restore_tpl().returning(|_| ());
        Service::mock(Box::new(tpl))
    }

    pub(crate) fn measurement() -> AuthorityMeasurement {
        AuthorityMeasurement::new(Service::mock(Box::new(MockProtocolServices::new())), tpl())
    }

    extern "efiapi" fn extend(
        _this: *const Tcg2Protocol,
        flags: u64,
        data: u64,
        size: u64,
        event: *const u8,
    ) -> efi::Status {
        assert_eq!(flags, 0);
        // SAFETY: The caller passes the live, fully initialized event payload of `size` bytes.
        let data = unsafe { core::slice::from_raw_parts(data as usize as *const u8, size as usize) };
        assert_eq!(data, authority_event_data(&[1, 2]));
        // SAFETY: The event was constructed by tcg_event and has the fixed 18-byte header.
        let header = unsafe { core::slice::from_raw_parts(event, 18) };
        assert_eq!(&header[4..8], &14u32.to_le_bytes());
        assert_eq!(&header[8..10], &1u16.to_le_bytes());
        assert_eq!(&header[10..14], &7u32.to_le_bytes());
        assert_eq!(&header[14..18], &VARIABLE_AUTHORITY.to_le_bytes());
        efi::Status::SUCCESS
    }

    #[test]
    fn test_secure_boot_measurement_encoding_and_deduplication() {
        let protocol = Box::leak(Box::new(Tcg2Protocol {
            get_capability: 0,
            get_event_log: 0,
            hash_log_extend_event: extend,
            submit_command: 0,
            get_active_pcr_banks: 0,
            set_active_pcr_banks: 0,
            get_result_of_set_active_pcr_banks: 0,
        }));
        let address = core::ptr::from_mut(protocol) as usize;
        let mut protocols = MockProtocolServices::new();
        protocols.expect_locate_interface().once().returning(move |guid| {
            assert_eq!(guid, Tcg2Protocol::PROTOCOL_GUID);
            Ok(ProtocolPtr::from_raw(address as *mut core::ffi::c_void).unwrap())
        });
        let measurement = AuthorityMeasurement::new(Service::mock(Box::new(protocols)), tpl());
        measurement.measure(&[1, 2]).unwrap();
        measurement.measure(&[1, 2]).unwrap();
        assert_eq!(measurement.measured.checked_lock().expect("test measurement lock should be available").len(), 1);
    }

    #[test]
    fn test_secure_boot_measurement_failure_remains_retryable() {
        let mut protocols = MockProtocolServices::new();
        protocols.expect_locate_interface().times(2).returning(|_| Err(ProtocolError::NotFound));
        let measurement = AuthorityMeasurement::new(Service::mock(Box::new(protocols)), tpl());
        for _ in 0..2 {
            assert_eq!(measurement.measure(&[1, 2]), Err(EfiError::NotFound));
            assert!(measurement.measured.checked_lock().expect("test measurement lock should be available").is_empty());
        }
    }

    #[test]
    fn test_secure_boot_measurement_provider_failure_remains_retryable() {
        extern "efiapi" fn fail(_: *const Tcg2Protocol, _: u64, _: u64, _: u64, _: *const u8) -> efi::Status {
            efi::Status::DEVICE_ERROR
        }
        let protocol = Box::leak(Box::new(Tcg2Protocol {
            get_capability: 0,
            get_event_log: 0,
            hash_log_extend_event: fail,
            submit_command: 0,
            get_active_pcr_banks: 0,
            set_active_pcr_banks: 0,
            get_result_of_set_active_pcr_banks: 0,
        }));
        let address = core::ptr::from_mut(protocol) as usize;
        let mut protocols = MockProtocolServices::new();
        protocols
            .expect_locate_interface()
            .times(2)
            .returning(move |_| Ok(ProtocolPtr::from_raw(address as *mut core::ffi::c_void).unwrap()));
        let measurement = AuthorityMeasurement::new(Service::mock(Box::new(protocols)), tpl());
        for _ in 0..2 {
            assert_eq!(measurement.measure(&[1, 2]), Err(EfiError::DeviceError));
            assert!(measurement.measured.checked_lock().expect("test measurement lock should be available").is_empty());
        }
    }

    #[test]
    fn test_secure_boot_measurement_rejects_locked_reservations() {
        let measurement = measurement();
        let _guard = measurement.measured.checked_lock().expect("test measurement lock should be available");
        #[cfg(debug_assertions)]
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| measurement.measure(&[1, 2]))).is_err());
        #[cfg(not(debug_assertions))]
        assert_eq!(measurement.measure(&[1, 2]), Err(EfiError::AccessDenied));
    }

    #[test]
    fn test_secure_boot_measurement_event_wire_layout() {
        let data = authority_event_data(&[3; 17]);
        assert_eq!(&data[..16], DATABASE_GUID.as_bytes());
        assert_eq!(&data[16..24], &2u64.to_le_bytes());
        assert_eq!(&data[24..32], &17u64.to_le_bytes());
        assert_eq!(&data[32..36], &[b'd', 0, b'b', 0]);
        let event = tcg_event(&data).unwrap();
        assert_eq!(event.len(), 18 + data.len());
        assert_eq!(&event[..4], &(event.len() as u32).to_le_bytes());
        assert_eq!(&event[18..], data);
    }
}
