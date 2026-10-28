//! Deferred MM communication buffer updates.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!

use alloc::boxed::Box;
use patina::{
    UEFI_PAGE_SIZE,
    component::service::{
        Service,
        uefi_services::{
            protocol::{Handle, ProtocolServices, ProtocolServicesExt, Tpl},
            tpl::TplServices,
        },
    },
    management_mode::protocol::mm_comm_buffer_update::MmCommBufferUpdateProtocol,
    uefi::{boot_services::tpl::Tpl as LockTpl, tpl_mutex::TplMutex},
};

use crate::config::{CommunicateBuffer, CommunicateBufferAccess};

#[derive(Clone, Copy)]
struct BufferUpdate {
    address: u64,
    size: usize,
    mailbox: u64,
}

/// One configured buffer and the latest pending firmware region description.
pub(super) struct ProtocolNotifyContext {
    buffer: CommunicateBuffer,
    pending: TplMutex<Option<BufferUpdate>, Service<dyn TplServices>>,
}

/// Registers notifications for an existing configured buffer.
///
/// The context is retained for the lifetime of the firmware callback.
pub(super) fn register_buffer_update_notify(
    protocols: Service<dyn ProtocolServices>,
    buffer: CommunicateBuffer,
    tpl: Service<dyn TplServices>,
) -> patina::error::Result<&'static ProtocolNotifyContext> {
    let context =
        Box::leak(Box::new(ProtocolNotifyContext { buffer, pending: TplMutex::new(tpl, LockTpl::NOTIFY, None) }));
    let context: &'static ProtocolNotifyContext = context;
    let callback_protocols = protocols.clone();
    protocols.on_protocol_installed::<MmCommBufferUpdateProtocol>(Tpl::Callback, move |handle| {
        handle_protocol_installed(&callback_protocols, handle, context);
    })?;
    Ok(context)
}

/// Applies the pending region under the buffer's shared transaction lock.
///
/// Busy buffers retain their pending update for the next communication call.
pub(super) fn apply_pending_buffer_update(context: &ProtocolNotifyContext) -> bool {
    let Ok(mut buffer) = context.buffer.try_lock() else {
        return false;
    };
    let Ok(mut pending) = context.pending.try_lock() else {
        return false;
    };
    let Some(update) = pending.take() else {
        return false;
    };
    // SAFETY: The installed firmware protocol transfers exclusive normal RAM.
    // The buffer guard excludes all clones during replacement and subsequent access.
    match unsafe { buffer.replace_firmware_region(update.address, update.size, update.mailbox) } {
        Ok(()) => {
            log::info!(target: "mm_comm", "Updated communication buffer {} in place", buffer.id());
            true
        }
        Err(error) => {
            log::error!(target: "mm_comm", "Rejected communication buffer {} update: {error:?}", buffer.id());
            false
        }
    }
}

fn handle_protocol_installed(
    protocols: &Service<dyn ProtocolServices>,
    handle: Handle,
    context: &ProtocolNotifyContext,
) {
    let protocol = match protocols.with_protocol_on::<MmCommBufferUpdateProtocol, _>(handle, |protocol| *protocol) {
        Ok(protocol) => protocol,
        Err(error) => {
            log::error!(target: "mm_comm", "Failed to read MM buffer update on handle {handle:?}: {error:?}");
            return;
        }
    };
    let Some(size) = protocol
        .updated_comm_buffer
        .number_of_pages
        .checked_mul(UEFI_PAGE_SIZE as u64)
        .and_then(|size| usize::try_from(size).ok())
    else {
        log::error!(target: "mm_comm", "MM communication buffer update size overflow");
        return;
    };
    let update = BufferUpdate {
        address: protocol.updated_comm_buffer.physical_start,
        size,
        mailbox: protocol.updated_comm_buffer.status,
    };
    if let Err(error) =
        CommunicateBufferAccess::validate_firmware_region(update.address, update.size, Some(update.mailbox))
    {
        log::error!(target: "mm_comm", "Invalid MM communication buffer update: {error:?}");
        return;
    }
    let Ok(mut pending) = context.pending.try_lock() else {
        log::error!(target: "mm_comm", "Could not record MM communication buffer update: pending slot busy");
        return;
    };
    if pending.replace(update).is_some() {
        log::warn!(target: "mm_comm", "Replacing previous pending communication buffer update");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::{CommunicateBufferStatus, mock_tpl_service};
    use core::{ffi::c_void, pin::Pin};
    use patina::{
        component::service::uefi_services::protocol::{
            MockProtocolServices, NotifyRegistration, ProtocolError, ProtocolPtr,
        },
        management_mode::{
            MmCommBufferStatus,
            protocol::mm_comm_buffer_update::{self, MmCommBuffer},
        },
    };

    fn test_context() -> ProtocolNotifyContext {
        ProtocolNotifyContext {
            buffer: CommunicateBuffer::new(Pin::new(Box::leak(Box::new([0u8; 4096]))), 4, mock_tpl_service()),
            pending: TplMutex::new(mock_tpl_service(), LockTpl::NOTIFY, None),
        }
    }

    #[repr(align(4096))]
    struct Page([u8; 4096]);

    fn update() -> BufferUpdate {
        BufferUpdate {
            address: Box::leak(Box::new(Page([0; 4096]))).0.as_mut_ptr() as u64,
            size: 4096,
            mailbox: core::ptr::from_mut(Box::leak(Box::new(MmCommBufferStatus::new()))) as u64,
        }
    }

    fn fake_handle() -> Handle {
        Handle::from_raw(core::ptr::NonNull::<c_void>::dangling().as_ptr()).unwrap()
    }

    fn protocols(update: BufferUpdate) -> MockProtocolServices {
        protocols_for(MmCommBufferUpdateProtocol {
            version: 1,
            updated_comm_buffer: MmCommBuffer {
                physical_start: update.address,
                number_of_pages: (update.size / UEFI_PAGE_SIZE) as u64,
                status: update.mailbox,
            },
        })
    }

    fn protocols_for(protocol: MmCommBufferUpdateProtocol) -> MockProtocolServices {
        let protocol = Box::leak(Box::new(protocol));
        let address = core::ptr::from_mut(protocol) as usize;
        let mut protocols = MockProtocolServices::new();
        protocols
            .expect_interface_on_handle()
            .withf(|_, guid| guid == &mm_comm_buffer_update::PROTOCOL_GUID)
            .returning(move |_, _| Ok(ProtocolPtr::from_raw(address as *mut c_void).unwrap()));
        protocols
    }

    fn notify(context: &ProtocolNotifyContext, update: BufferUpdate) {
        let service: Service<dyn ProtocolServices> = Service::mock(Box::new(protocols(update)));
        handle_protocol_installed(&service, fake_handle(), context);
    }

    #[test]
    fn test_mm_buffer_update_changes_every_alias_in_place() {
        let context = test_context();
        let alias = context.buffer.clone();
        let update = update();
        notify(&context, update);
        assert!(apply_pending_buffer_update(&context));
        let mut access = alias.try_lock().unwrap();
        assert_eq!(access.as_ptr() as u64, update.address);
        assert_eq!(access.len(), update.size);
        access.set_mm_return_status(3, 64).unwrap();
        assert!(matches!(context.buffer.try_lock(), Err(CommunicateBufferStatus::Busy)));
        drop(access);
        assert_eq!(context.buffer.try_lock().unwrap().get_mm_return_status().unwrap(), (3, 64));
        assert!(context.pending.lock().is_none());
    }

    #[test]
    fn test_mm_buffer_update_defers_while_alias_is_active() {
        let context = test_context();
        let alias = context.buffer.clone();
        let access = alias.try_lock().unwrap();
        notify(&context, update());
        assert!(!apply_pending_buffer_update(&context));
        assert!(context.pending.lock().is_some());
        drop(access);
        assert!(apply_pending_buffer_update(&context));
    }

    #[test]
    fn test_mm_buffer_update_latest_notification_wins() {
        let context = test_context();
        notify(&context, update());
        let latest = update();
        notify(&context, latest);
        assert!(apply_pending_buffer_update(&context));
        assert_eq!(context.buffer.try_lock().unwrap().as_ptr() as u64, latest.address);
        assert!(!apply_pending_buffer_update(&context));
    }

    #[test]
    fn test_mm_buffer_update_repeat_preserves_contents_and_lock() {
        let context = test_context();
        let update = update();
        notify(&context, update);
        assert!(apply_pending_buffer_update(&context));
        context.buffer.try_lock().unwrap().set_mm_return_status(7, 32).unwrap();
        notify(&context, update);
        assert!(apply_pending_buffer_update(&context));
        assert_eq!(context.buffer.try_lock().unwrap().get_mm_return_status().unwrap(), (7, 32));
    }

    #[test]
    fn test_mm_buffer_update_shared_contexts_keep_one_transaction_lock() {
        let first = test_context();
        let second = ProtocolNotifyContext {
            buffer: first.buffer.clone(),
            pending: TplMutex::new(mock_tpl_service(), LockTpl::NOTIFY, None),
        };
        let update = update();
        notify(&first, update);
        notify(&second, update);
        assert!(apply_pending_buffer_update(&first));
        first.buffer.try_lock().unwrap().set_mm_return_status(5, 80).unwrap();
        let guard = first.buffer.try_lock().unwrap();
        assert!(!apply_pending_buffer_update(&second));
        drop(guard);
        assert!(apply_pending_buffer_update(&second));
        assert_eq!(second.buffer.try_lock().unwrap().get_mm_return_status().unwrap(), (5, 80));
    }

    #[test]
    fn test_mm_buffer_update_pending_slot_contention_defers_application() {
        let context = test_context();
        notify(&context, update());
        let pending = context.pending.lock();
        assert!(!apply_pending_buffer_update(&context));
        assert!(pending.is_some());
        drop(pending);
        assert!(apply_pending_buffer_update(&context));
    }

    #[test]
    fn test_mm_buffer_update_can_return_to_a_previous_region() {
        let context = test_context();
        let first = update();
        let second = update();
        for update in [first, second, first] {
            notify(&context, update);
            assert!(apply_pending_buffer_update(&context));
            assert_eq!(context.buffer.try_lock().unwrap().as_ptr() as u64, update.address);
        }
    }

    #[test]
    fn test_mm_buffer_update_rejects_overlap_without_changing_buffer() {
        let context = test_context();
        let update = update();
        notify(&context, update);
        assert!(apply_pending_buffer_update(&context));
        let replacement = self::update();
        for overlap in [
            BufferUpdate { mailbox: replacement.mailbox, ..update },
            BufferUpdate { mailbox: update.mailbox, ..replacement },
            BufferUpdate { mailbox: update.address, ..replacement },
        ] {
            notify(&context, overlap);
            assert!(!apply_pending_buffer_update(&context));
            assert_eq!(context.buffer.try_lock().unwrap().as_ptr() as u64, update.address);
            assert!(context.pending.lock().is_none());
        }
    }

    #[test]
    fn test_mm_buffer_update_ignores_invalid_descriptors() {
        let context = test_context();
        let valid = update();
        for invalid in [
            BufferUpdate { address: 0, ..valid },
            BufferUpdate { address: valid.address + 1, ..valid },
            BufferUpdate { size: 0, ..valid },
            BufferUpdate { size: usize::MAX, ..valid },
            BufferUpdate { mailbox: valid.address, ..valid },
            BufferUpdate { mailbox: 0, ..valid },
        ] {
            notify(&context, invalid);
            assert!(context.pending.lock().is_none());
        }
    }

    #[test]
    fn test_mm_buffer_update_page_count_overflow_preserves_pending_region() {
        let context = test_context();
        let valid = update();
        notify(&context, valid);
        let service: Service<dyn ProtocolServices> =
            Service::mock(Box::new(protocols_for(MmCommBufferUpdateProtocol {
                version: 1,
                updated_comm_buffer: MmCommBuffer {
                    physical_start: valid.address,
                    number_of_pages: u64::MAX,
                    status: valid.mailbox,
                },
            })));
        handle_protocol_installed(&service, fake_handle(), &context);
        assert!(apply_pending_buffer_update(&context));
        assert_eq!(context.buffer.try_lock().unwrap().as_ptr() as u64, valid.address);
    }

    #[test]
    fn test_mm_buffer_update_ignores_missing_interface() {
        let context = test_context();
        let mut protocols = MockProtocolServices::new();
        protocols.expect_interface_on_handle().once().returning(|_, _| Err(ProtocolError::NotFound));
        let service: Service<dyn ProtocolServices> = Service::mock(Box::new(protocols));
        handle_protocol_installed(&service, fake_handle(), &context);
        assert!(context.pending.lock().is_none());
    }

    #[test]
    fn test_mm_buffer_update_registration_delivers_existing_protocol() {
        let mut protocols = protocols(update());
        protocols.expect_register_install_notify().once().returning(|_, _, mut callback| {
            callback(fake_handle());
            Ok(NotifyRegistration::from_raw(core::ptr::null_mut(), core::ptr::null_mut(), core::ptr::null_mut()))
        });
        let context = register_buffer_update_notify(
            Service::mock(Box::new(protocols)),
            test_context().buffer,
            mock_tpl_service(),
        )
        .unwrap();
        assert!(context.pending.lock().is_some());
        assert!(apply_pending_buffer_update(context));
    }

    #[test]
    fn test_mm_buffer_update_registration_propagates_failure() {
        let mut protocols = MockProtocolServices::new();
        protocols.expect_register_install_notify().once().returning(|_, _, _| Err(ProtocolError::OutOfResources));
        assert!(
            register_buffer_update_notify(
                Service::mock(Box::new(protocols)),
                test_context().buffer,
                mock_tpl_service(),
            )
            .is_err()
        );
    }
}
