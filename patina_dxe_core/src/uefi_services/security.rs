//! Native image-security handlers, called in addition to the architectural protocols.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use alloc::{sync::Arc, vec::Vec};
use patina::{
    component::service::{
        IntoService,
        security::{ImageAuthentication, ImageSecurityHandler, SecurityServices},
    },
    error::{EfiError, Result},
    standard::efi,
};

use crate::tpl_mutex::TplMutex;

static HANDLERS: TplMutex<Vec<Arc<dyn ImageSecurityHandler>>> =
    TplMutex::new(efi::TPL_NOTIFY, Vec::new(), "ImageSecurityHandlers");

#[derive(IntoService)]
#[service(dyn SecurityServices)]
pub(crate) struct CoreSecurityServices;

impl SecurityServices for CoreSecurityServices {
    fn register_handler(&self, handler: Arc<dyn ImageSecurityHandler>) -> Result<()> {
        let mut handlers = HANDLERS.checked_lock()?;
        handlers.try_reserve(1).map_err(|error| {
            log::error!("Unable to register image-security handler: {error}");
            EfiError::OutOfResources
        })?;
        handlers.push(handler);
        Ok(())
    }
}

pub(crate) fn authenticate(request: &ImageAuthentication<'_>) -> Result<()> {
    let snapshot = {
        let handlers = HANDLERS.checked_lock()?;
        let mut snapshot = Vec::new();
        snapshot.try_reserve(handlers.len()).map_err(|error| {
            log::error!("Unable to snapshot image-security handlers: {error}");
            EfiError::OutOfResources
        })?;
        snapshot.extend(handlers.iter().cloned());
        snapshot
    };
    // Never hold the registry lock across cryptography, protocol calls, or recursive image loads.
    for handler in snapshot {
        handler.authenticate(request)?;
    }
    Ok(())
}

#[cfg(test)]
pub(crate) fn clear_handlers() {
    HANDLERS.checked_lock().expect("test security handler registry should be available").clear();
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
mod tests {
    use super::*;
    use core::sync::atomic::{AtomicUsize, Ordering};

    struct Handler {
        calls: Arc<AtomicUsize>,
        ordinal: usize,
        deny: bool,
    }

    impl ImageSecurityHandler for Handler {
        fn authenticate(&self, _: &ImageAuthentication<'_>) -> Result<()> {
            assert_eq!(self.calls.fetch_add(1, Ordering::SeqCst), self.ordinal);
            if self.deny { Err(EfiError::AccessDenied) } else { Ok(()) }
        }
    }

    struct ReentrantHandler {
        calls: AtomicUsize,
        nested: Arc<AtomicUsize>,
    }

    impl ImageSecurityHandler for ReentrantHandler {
        fn authenticate(&self, request: &ImageAuthentication<'_>) -> Result<()> {
            if self.calls.fetch_add(1, Ordering::SeqCst) == 0 {
                CoreSecurityServices.register_handler(Arc::new(Handler {
                    calls: self.nested.clone(),
                    ordinal: 0,
                    deny: false,
                }))?;
                authenticate(request)?;
            }
            Ok(())
        }
    }

    fn request() -> ImageAuthentication<'static> {
        ImageAuthentication { image: &[], from_firmware_volume: false, boot_policy: false }
    }

    #[test]
    fn test_security_services_empty_order_and_first_denial() {
        crate::test_support::with_global_lock(|| {
            let _cleanup = crate::test_support::StateGuard::new(clear_handlers);
            assert!(HANDLERS.checked_lock().expect("test registry should be available").is_empty());
            assert_eq!(authenticate(&request()), Ok(()));
            let calls = Arc::new(AtomicUsize::new(0));
            for ordinal in 0..3 {
                CoreSecurityServices
                    .register_handler(Arc::new(Handler { calls: calls.clone(), ordinal, deny: ordinal == 1 }))
                    .unwrap();
            }
            assert_eq!(authenticate(&request()), Err(EfiError::AccessDenied));
            assert_eq!(calls.load(Ordering::SeqCst), 2);
        })
        .unwrap();
    }

    #[test]
    fn test_security_services_callbacks_run_without_registry_lock() {
        crate::test_support::with_global_lock(|| {
            let _cleanup = crate::test_support::StateGuard::new(clear_handlers);
            assert!(HANDLERS.checked_lock().expect("test registry should be available").is_empty());
            let nested = Arc::new(AtomicUsize::new(0));
            let handler = Arc::new(ReentrantHandler { calls: AtomicUsize::new(0), nested: nested.clone() });
            CoreSecurityServices.register_handler(handler.clone()).unwrap();
            assert_eq!(authenticate(&request()), Ok(()));
            assert_eq!(handler.calls.load(Ordering::SeqCst), 2);
            // The new handler runs in the recursive load, but not the outer snapshot.
            assert_eq!(nested.load(Ordering::SeqCst), 1);
        })
        .unwrap();
    }
}
