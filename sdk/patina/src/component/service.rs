//! A module for the [Service] param type and any common service traits.
//!
//! The [Service] [Param] is a wait for components to produce and consume services defined by an interface (`Trait`)
//! that is agnostic to the underlying concrete implementation. It also allows a single concrete type to be used as
//! multiple services by implementing multiple traits on the same type and specifying the services trait(s) in the
//! [`IntoService`] derive macro.
//!
//! To simplify the management of services, the underlying datum is *always* readonly. This means that only `&self`
//! interface methods will be available to consumers of the service. If a service needs to be mutable, it should use
//! interior mutability to achieve this.
//!
//! Handles share ownership of type-erased backing data, allowing one service to retain another service
//! without knowing its concrete implementation or borrowing the storage. Owned implementations are
//! destroyed when their last owner is dropped; externally owned static implementations are not destroyed.
//! Ownership cycles and handles retained in static cells keep implementations alive.
//!
//! Firmware must retain its services for as long as callbacks or runtime consumers can use them, and
//! must not release the last owner after `ExitBootServices`, when deallocation is unavailable.
//!
//! Similar to other [Param] implementations, any component that consumes a service will not be dispatched until the
//! services is produced, which allows for ordered dispatch of components that depend on each other. As mentioned
//! above, if one service depends on another service, not only will the service be produced first, but that service
//! can also be consumed by the dependent service before being produced
//!
//! ## Protocol Backwards Compatability
//!
//! While not suggested, it is possible to publish a service as an EDKII compatible protocol for backwards
//! compatability with existing EDKII code, allowing for a rust service to be consumed by an EDKII driver. As mentioned
//! multiple times, this is **only** for backwards compatability and should be avoided if possible. Any rust to rust
//! component interactions should be done through the [Service] [Param] type. Please review the [`IntoService`] trait on
//! how to register a service as an EDKII protocol.
//!
//! The protocol function backing an EDKII-compatible service is a bare `extern "efiapi"` function pointer with no
//! context parameter, so it cannot capture a [Service] the way a closure-based callback can. [`cell::ServiceCell`]
//! provides a way to bridge a component's injected [Service] into that context-free function. See its documentation
//! for details and an example.
//!
//! ## Example
//!
//! ### Implementing a Service
//!
//! See [`IntoService`][patina_macro::IntoService] macro for more information on how to implement a service. While the
//! macro does not have to be used, it is recommended to ensure the service is implemented correctly.
//!
//! ### Basic Service Usage
//!
//! ```rust
//! use patina::{
//!    error::Result,
//!    component::{
//!        service::{IntoService, Service},
//!        Storage,
//!    }
//! };
//!
//! trait MyService: Send + Sync {}
//!
//! #[derive(IntoService)]
//! #[service(dyn MyService)]
//! struct MyServiceImpl;
//!
//! impl MyService for MyServiceImpl {}
//!
//! // This component will not be dispatched until the `MyService` service is produced.
//! fn my_component(service: Service<dyn MyService>) -> Result<()> {
//!     Ok(())
//! }
//!
//! // This component will be dispatched before `my_component` as it produces the `MyService` service.
//! fn service_producer(storage: &mut Storage) -> Result<()> {
//!     let service = MyServiceImpl;
//!     storage.add_service(service);
//!
//!     Ok(())
//! }
//! ```
//!
//! ## Services Consuming Other Services
//!
//! The below example shows how one service can consume another service when producing the service.
//!
//! ```rust
//! use patina::{
//!   error::Result,
//!   component::{
//!     service::{IntoService, Service},
//!     Storage,
//!   }
//! };
//!
//! trait Service1: Send + Sync {}
//! trait Service2: Send + Sync {}
//!
//! #[derive(IntoService)]
//! #[service(dyn Service1)]
//! struct Service1Impl;
//!
//! impl Service1 for Service1Impl {}
//!
//! #[derive(IntoService)]
//! #[service(dyn Service2)]
//! struct Service2Impl {
//!    service1: Service<dyn Service1>,
//! }
//!
//! impl Service2 for Service2Impl {}
//!
//! fn service1_producer(storage: &mut Storage) -> Result<()> {
//!   let service = Service1Impl;
//!   storage.add_service(service);
//!   Ok(())
//! }
//!
//! fn service2_producer(storage: &mut Storage, service1: Service<dyn Service1>) -> Result<()> {
//!   let service = Service2Impl { service1 };
//!   storage.add_service(service);
//!   Ok(())
//! }
//! ```
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use alloc::{borrow::Cow, boxed::Box, sync::Arc};
use core::{any::Any, fmt::Debug, marker::PhantomData, ops::Deref};

use crate::component::{
    metadata::MetaData,
    params::Param,
    storage::{Storage, UnsafeStorageCell},
};

pub mod cell;
pub mod dxe_dispatch;
pub mod memory;
pub mod perf_timer;
pub mod performance;
pub mod uefi_services;

pub use patina_macro::IntoService;

/// A trait that allows the implementor to register a service with the underlying [Storage].
pub trait IntoService {
    /// Registers the service with the underlying [Storage], consuming self
    fn register(self, storage: &mut Storage);
    /// Helper function to register the service.
    ///
    /// The erased value must contain an `Arc<S>` for an owned service or an `&'static S`
    /// for an externally owned static service.
    ///
    /// ## Example
    ///
    /// ``` rust
    /// extern crate alloc;
    ///
    /// use alloc::sync::Arc;
    /// use patina::component::{Storage, service::IntoService};
    ///
    /// struct MyStruct;
    ///
    /// trait Service: Send + Sync {}
    ///
    /// impl Service for MyStruct {}
    ///
    /// impl IntoService for MyStruct {
    ///   fn register(self, storage: &mut Storage) {
    ///     let service: Arc<dyn Service> = Arc::new(self);
    ///     Self::register_service::<dyn Service>(storage, Arc::new(service));
    ///   }
    /// }
    ///
    /// ```
    fn register_service<S: ?Sized + 'static>(storage: &mut Storage, service: Arc<dyn Any + Send + Sync>) {
        let id = storage.register_service::<S>();
        storage.insert_service(id, service);
    }
}

/// A shared service that can be used as a parameter to a [Component](super::Component).
///
/// The underlying service that this object wraps can be either a concrete type such as a struct or enum, or a dyn
/// trait object. In nearly all cases, the service should be a dyn trait object so that consumers of the service can
/// rely on the service being the same regardless of the underlying implementation.
///
/// Handles own their service and can outlive the storage that produced them. Cloning a handle shares
/// ownership; an owned implementation is dropped when its last owner is dropped. References obtained
/// through a handle borrow that handle rather than having a static lifetime.
///
/// Implementations must be thread-safe. Interior mutability through `&self` does not bypass this
/// requirement:
///
/// ```compile_fail
/// use patina::component::service::Service;
/// use std::cell::Cell;
///
/// let service = Service::mock(Box::new(Cell::new(0u32)));
/// ```
///
/// While implementing [`IntoService`] is possible, it is advised to use the [`IntoService`](patina_macro::IntoService)
/// derive macro, which also provides more information.
pub struct Service<T: ?Sized + 'static> {
    value: Arc<dyn Any + Send + Sync>,
    _marker: core::marker::PhantomData<T>,
}

impl<T: ?Sized + 'static> Service<T> {
    /// Creates an owned service for testing.
    ///
    /// The mock is dropped when the last handle is dropped, allowing mock frameworks to verify
    /// unmet expectations. Retaining handles in static cells or ownership cycles prevents this
    /// automatic verification.
    ///
    /// ## Example
    ///
    /// ```rust
    /// use patina::component::service::Service;
    ///
    /// trait Service1: Send + Sync {
    ///   fn do_something(&self) -> u32;
    /// }
    ///
    /// struct MockService;
    ///
    ///   impl Service1 for MockService {
    ///     fn do_something(&self) -> u32 {
    ///       42
    ///     }
    ///   }
    ///
    /// fn my_component_to_test(service: Service<dyn Service1>) {
    ///   let _ = service.do_something();
    /// }
    ///
    /// #[test]
    /// fn test_my_component() {
    ///   // Create a mock, maybe use mockall?
    ///   let service = Service::mock(Box::new(MockService));
    ///   my_component_to_test(service);
    /// }
    /// ```
    #[allow(clippy::test_attr_in_doctest)]
    pub fn mock(value: Box<T>) -> Self
    where
        T: Send + Sync,
    {
        let value: Arc<T> = Arc::from(value);
        Self { value: Arc::new(value), _marker: PhantomData }
    }
}

impl<T: ?Sized + 'static> From<Arc<dyn Any + Send + Sync>> for Service<T> {
    fn from(value: Arc<dyn Any + Send + Sync>) -> Self {
        Self { value, _marker: PhantomData }
    }
}

impl<T: ?Sized + 'static> Deref for Service<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        if let Some(value) = self.value.downcast_ref::<Arc<T>>() {
            value.as_ref()
        } else {
            self.value
                .downcast_ref::<&'static T>()
                .copied()
                .unwrap_or_else(|| panic!("Service should be of type {}", super::type_name::normalized::<T>()))
        }
    }
}

impl<T: ?Sized + 'static> Clone for Service<T> {
    fn clone(&self) -> Self {
        Self { value: Arc::clone(&self.value), _marker: PhantomData }
    }
}

impl<T: ?Sized + 'static> Debug for Service<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        // Note: The wrapped value is type-erased, so only the type name can be shown, not its contents.
        f.debug_struct("Service").field("type", &super::type_name::normalized::<T>()).finish()
    }
}

// SAFETY: Service<T> parameter provides access to registered services.
// State tracks the service ID. Validates service availability before access.
unsafe impl<T: ?Sized + 'static> Param for Service<T> {
    type State = usize;
    type Item<'storage, 'state> = Service<T>;

    unsafe fn get_param<'storage, 'state>(
        state: &'state Self::State,
        storage: UnsafeStorageCell<'storage>,
    ) -> Self::Item<'storage, 'state> {
        // SAFETY: State was validated by validate() to contain a valid service ID.
        // UnsafeStorageCell provides exclusive access to storage under Param protocol.
        Service::from(unsafe {
            storage
                .storage()
                .get_raw_service(*state)
                .unwrap_or_else(|| {
                    panic!("Could not find Service value with id [{}] even though it was just validated.", *state)
                })
                .clone()
        })
    }

    fn validate(state: &Self::State, storage: UnsafeStorageCell) -> bool {
        // SAFETY: Storage access is controlled by UnsafeStorageCell. Just checking service existence.
        unsafe { storage.storage() }.get_raw_service(*state).is_some()
    }

    fn init_state(storage: &mut Storage, _meta: &mut MetaData) -> Result<Self::State, Cow<'static, str>> {
        Ok(storage.register_service::<T>())
    }
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
mod tests {
    use super::{IntoService, *};

    #[mockall::automock]
    trait CheckedService: Send + Sync {
        fn value(&self) -> u32;
    }

    #[test]
    #[should_panic(expected = "fewer than expected")]
    fn test_service_mock_checks_unmet_expectations_on_drop() {
        let mut mock = MockCheckedService::new();
        mock.expect_value().once().return_const(42u32);
        let service: Service<dyn CheckedService> = Service::mock(Box::new(mock));
        drop(service);
    }

    #[test]
    #[should_panic(expected = "fewer than expected")]
    fn test_service_mock_checks_partially_met_expectations_on_last_drop() {
        let mut mock = MockCheckedService::new();
        mock.expect_value().times(2).return_const(42u32);
        let service: Service<dyn CheckedService> = Service::mock(Box::new(mock));
        let other = service.clone();
        assert_eq!(service.value(), 42);
        drop(service);
        drop(other);
    }

    #[test]
    fn test_service_mock_can_meet_expectation_after_original_handle_drops() {
        let mut mock = MockCheckedService::new();
        mock.expect_value().once().return_const(42u32);
        let service: Service<dyn CheckedService> = Service::mock(Box::new(mock));
        let other = service.clone();
        drop(service);
        assert_eq!(other.value(), 42);
        drop(other);
    }

    #[test]
    fn test_service_mock_can_be_used_and_dropped_on_another_thread() {
        let mut mock = MockCheckedService::new();
        mock.expect_value().once().return_const(42u32);
        let service: Service<dyn CheckedService> = Service::mock(Box::new(mock));
        let other = service.clone();
        drop(service);
        std::thread::spawn(move || {
            assert_eq!(other.value(), 42);
        })
        .join()
        .expect("service owner should safely transfer to another thread");
    }

    #[test]
    fn test_service_interfaces_share_ownership_beyond_storage() {
        use crate as patina;
        use core::sync::atomic::{AtomicUsize, Ordering};

        trait First: Send + Sync {}
        trait Second: Send + Sync {}

        #[derive(IntoService)]
        #[service(dyn First, dyn Second)]
        struct Shared(Arc<AtomicUsize>);

        impl First for Shared {}
        impl Second for Shared {}
        impl Drop for Shared {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        let drops = Arc::new(AtomicUsize::new(0));
        let mut storage = Storage::new();
        storage.add_service(Shared(drops.clone()));
        let first = storage.get_service::<dyn First>().unwrap();
        let second = storage.get_service::<dyn Second>().unwrap();
        drop(storage);
        assert_eq!(drops.load(Ordering::SeqCst), 0);
        drop(first);
        assert_eq!(drops.load(Ordering::SeqCst), 0);
        drop(second);
        assert_eq!(drops.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn test_service_derive_service_macro() {
        use crate as patina;

        trait MyService: Send + Sync {
            fn do_something(&self) -> u32;
        }

        trait MyService2: Send + Sync {
            fn do_something2(&self) -> u32;
        }

        #[derive(IntoService)]
        #[service(dyn MyService)]
        struct MyServiceImpl;

        impl MyService for MyServiceImpl {
            fn do_something(&self) -> u32 {
                42
            }
        }

        #[derive(IntoService)]
        #[service(dyn MyService2)]
        struct MyService2Impl {
            inner: Service<dyn MyService>,
        }

        impl MyService2 for MyService2Impl {
            fn do_something2(&self) -> u32 {
                self.inner.do_something()
            }
        }

        let mut storage = Storage::new();
        storage.add_service(MyServiceImpl);

        let s = storage.get_service::<dyn MyService>().unwrap();
        assert_eq!(42, s.do_something());

        storage.add_service(MyService2Impl { inner: s });
        let s2 = storage.get_service::<dyn MyService2>().unwrap();
        assert_eq!(42, s2.do_something2());

        storage.add_service(MyServiceImpl);

        #[derive(IntoService)]
        #[service(SomeStruct)]
        struct SomeStruct {
            x: u32,
        }

        storage.add_service(SomeStruct { x: 1 });
        let s3 = storage.get_service::<SomeStruct>().unwrap();
        assert_eq!(1, s3.x);
    }

    #[test]
    fn test_available_service_validates_true() {
        use crate as patina;

        trait MyService: Send + Sync {
            fn do_something(&self) -> u32;
        }

        #[derive(IntoService)]
        #[service(dyn MyService)]
        struct MyServiceImpl;

        impl MyService for MyServiceImpl {
            fn do_something(&self) -> u32 {
                42
            }
        }

        let mut storage = Storage::default();
        let mut mock_metadata = MetaData::new::<i32>();

        let id = <Service<dyn MyService> as Param>::init_state(&mut storage, &mut mock_metadata).unwrap();

        storage.add_service(MyServiceImpl);

        assert!(<Service<dyn MyService> as Param>::try_validate(&id, (&storage).into()).is_ok());
        // SAFETY: Test code - Service<dyn MyService> has been validated and is available in storage.
        let service = unsafe { <Service<dyn MyService> as Param>::get_param(&id, (&storage).into()) };
        assert_eq!(42, service.do_something());
    }

    #[test]
    fn test_missing_service_validates_false() {
        trait MyService: Send + Sync {
            #[allow(dead_code)]
            fn do_something(&self) -> u32;
        }

        let mut storage = Storage::default();
        let mut mock_metadata = MetaData::new::<i32>();

        let id = <Service<dyn MyService> as Param>::init_state(&mut storage, &mut mock_metadata).unwrap();
        assert!(<Service<dyn MyService> as Param>::try_validate(&id, (&storage).into()).is_err());
    }

    #[test]
    #[should_panic]
    fn test_get_param_without_validate_should_panic_when_missing() {
        trait MyService: Send + Sync {
            #[allow(dead_code)]
            fn do_something(&self) -> u32;
        }

        let storage = Storage::default();
        // SAFETY: Test code - intentionally calling get_param without validation to test panic behavior.
        let _service =
            unsafe { <Service<dyn MyService> as Param>::get_param(&0, UnsafeStorageCell::new_readonly(&storage)) };
    }

    #[test]
    fn test_mocking_works() {
        trait MyService: Send + Sync {
            fn do_something(&self) -> u32;
        }

        struct MockService;

        impl MyService for MockService {
            fn do_something(&self) -> u32 {
                42
            }
        }
        let service: Service<dyn MyService> = Service::mock(Box::new(MockService));
        assert_eq!(42, service.do_something());
    }

    #[test]
    fn test_service_handles_can_be_cloned() {
        trait MyService: Send + Sync {
            fn do_something(&self) -> u32;
        }

        struct MockService;

        impl MyService for MockService {
            fn do_something(&self) -> u32 {
                42
            }
        }

        fn consume_service(service: Service<dyn MyService>) {
            assert_eq!(42, service.do_something());
        }

        let service: Service<dyn MyService> = Service::mock(Box::new(MockService));
        consume_service(service.clone());
        consume_service(service);
    }

    #[test]
    fn test_service_debug_shows_type_name_not_value() {
        trait MyService: Send + Sync {}

        struct MockService;

        impl MyService for MockService {}

        let service: Service<dyn MyService> = Service::mock(Box::new(MockService));
        let debug_str = alloc::format!("{service:?}");
        assert!(debug_str.contains("Service"));
        assert!(debug_str.contains("MyService"));
    }

    #[test]
    fn test_basic_static_support() {
        use crate as patina;
        trait MyService: Send + Sync {
            fn do_something(&self) -> u32;
        }

        #[derive(IntoService)]
        #[service(dyn MyService)]
        struct MockService {
            a: u32,
        }

        impl MockService {
            const fn new(a: u32) -> Self {
                Self { a }
            }
        }

        impl MyService for MockService {
            fn do_something(&self) -> u32 {
                self.a
            }
        }

        static MY_SERVICE: MockService = MockService::new(42);

        let mut storage = Storage::default();
        storage.add_service(&MY_SERVICE);

        let service = storage.get_service::<dyn MyService>().unwrap();
        assert_eq!(42, service.do_something());
    }
}
