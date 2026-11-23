//! Secure Boot policy gating tests.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use super::*;
use crate::{measurement::tests::measurement, test_support::*};
use alloc::{boxed::Box, vec};
use patina::{
    crypto::{hash::MockHash, signature::MockSignature},
    uefi::runtime_services::MockRuntimeServices,
};

fn handler(runtime: MockRuntimeServices) -> SecureBootHandler<MockRuntimeServices> {
    SecureBootHandler {
        hash: Service::mock(Box::new(MockHash::new())),
        signature: Service::mock(Box::new(MockSignature::new())),
        runtime,
        measurement: measurement(),
    }
}

fn request(image: &[u8]) -> ImageAuthentication<'_> {
    ImageAuthentication { image, from_firmware_volume: false, boot_policy: false }
}

#[test]
fn test_secure_boot_component_registers_handler_and_propagates_failure() {
    use patina::component::service::{security::MockSecurityServices, uefi_services::protocol::MockProtocolServices};

    for result in [Ok(()), Err(EfiError::OutOfResources)] {
        let mut security = MockSecurityServices::new();
        security.expect_register_handler().once().return_once(move |handler| {
            assert_eq!(
                handler.authenticate(&ImageAuthentication { from_firmware_volume: true, ..request(&[]) }),
                Ok(())
            );
            result
        });
        assert_eq!(
            SecureBootComponent::new().entry_point(
                Service::mock(Box::new(security)),
                Service::mock(Box::new(MockHash::new())),
                Service::mock(Box::new(MockSignature::new())),
                Service::mock(Box::new(MockProtocolServices::new())),
                crate::measurement::tests::tpl(),
                StandardRuntimeServices::new_uninit(),
            ),
            result
        );
    }
}

#[test]
fn test_secure_boot_component_fv_bypass_does_not_read_variables() {
    let handler = handler(MockRuntimeServices::new());
    assert_eq!(handler.authenticate(&ImageAuthentication { from_firmware_volume: true, ..request(&[]) }), Ok(()));
}

#[test]
fn test_secure_boot_component_absent_or_disabled() {
    let mut runtime = MockRuntimeServices::new();
    runtime.expect_get_variable::<Vec<u8>>().once().returning(|_, _, _| Err(efi::Status::NOT_FOUND));
    assert_eq!(handler(runtime).authenticate(&request(&[])), Ok(()));

    let mut runtime = MockRuntimeServices::new();
    runtime.expect_get_variable::<Vec<u8>>().returning(|_, _, _| Ok((vec![0], 0)));
    assert_eq!(handler(runtime).authenticate(&request(&[])), Ok(()));
}

#[test]
fn test_secure_boot_component_variable_failure_denies() {
    let mut runtime = MockRuntimeServices::new();
    runtime.expect_get_variable::<Vec<u8>>().returning(|_, _, _| Err(efi::Status::DEVICE_ERROR));
    assert_eq!(handler(runtime).authenticate(&request(&[])), Err(EfiError::AccessDenied));
}

#[test]
fn test_secure_boot_component_malformed_state_denies() {
    for value in [vec![], vec![2], vec![1, 0]] {
        let mut runtime = MockRuntimeServices::new();
        runtime.expect_get_variable::<Vec<u8>>().once().returning(move |_, _, _| Ok((value.clone(), 0)));
        assert_eq!(handler(runtime).authenticate(&request(&[])), Err(EfiError::AccessDenied));
    }
}

#[test]
fn test_secure_boot_component_enabled_reads_databases_and_verifies() {
    let db = list(SHA256, &[0xaa; 32], false);
    let mut runtime = MockRuntimeServices::new();
    runtime.expect_get_variable::<Vec<u8>>().returning(move |name, namespace, _| {
        if name == char16!("SecureBoot") {
            assert_eq!(*namespace, BinaryGuid::from_string("8be4df61-93ca-11d2-aa0d-00e098032b8c").into_inner());
            Ok((vec![1], 0))
        } else if name == char16!("db") {
            assert_eq!(*namespace, DATABASE_GUID.into_inner());
            Ok((db.clone(), 0))
        } else {
            assert_eq!(name, char16!("dbx"));
            Err(efi::Status::NOT_FOUND)
        }
    });
    let mut handler = handler(runtime);
    handler.hash = Service::mock(Box::new(hash()));
    assert_eq!(handler.authenticate(&request(&pe(false))), Ok(()));
}
