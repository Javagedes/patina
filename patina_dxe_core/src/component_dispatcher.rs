extern crate alloc;

use core::ptr::NonNull;

use crate::tpl_lock::TplMutex;
use patina::{
    boot_services::StandardBootServices,
    component::{IntoComponent, Storage, service::IntoService},
    pi::hob::HobList,
    runtime_services::StandardRuntimeServices,
};
use r_efi::efi;

use alloc::{boxed::Box, vec::Vec};

/// A trait to be implemented by the platform to register additional components, configurations, and services.
///
/// Allocations are available when these callbacks are invoked.
///
/// ## Example
///
/// ```rust
/// use patina_dxe_core::*;
/// struct MyPlatform;
///
/// impl ComponentInfo for MyPlatform {
///   fn configs(mut add: Add<Config>) {
///     add.config(32u32);
///     add.config(true);
///   }
/// }
/// ```
#[cfg_attr(test, mockall::automock)]
pub trait ComponentInfo: Sized {
    /// A platform callback to register components with the core.
    fn components<'a>(_add: Add<'a, Component>) {}

    /// A platform callback to register configurations with the core.
    fn configs<'a>(_add: Add<'a, Config>) {}

    /// A platform callback to register services with the core.
    fn services<'a>(_add: Add<'a, Service>) {}
}

/// A marker trait to limit [Add] methods to only adding [Component](patina::component::Component)s
pub struct Component;
/// A marker trait to limit [Add] methods to only adding Configs.
pub struct Config;
/// A marker trait to limit [Add] methods to only adding [Service](patina::component::service::Service)s
pub struct Service;

/// A struct used to allow controlled access to the Core's storage.
pub struct Add<'a, L> {
    /// The component dispatcher to add to.
    pub dispatcher: &'a mut ComponentDispatcher,
    /// Marker to limit what methods are available on this struct.
    _limiter: core::marker::PhantomData<L>,
}

impl<T> Add<'_, T> {
    /// Creates a new [Add] struct.
    pub fn new<'a>(dispatcher: &'a mut ComponentDispatcher) -> Add<'a, T> {
        Add { dispatcher, _limiter: core::marker::PhantomData }
    }
}

impl Add<'_, Component> {
    /// Adds a component to the core's component list.
    pub fn component<I>(&mut self, component: impl IntoComponent<I>) {
        let mut component = component.into_component();
        component.initialize(&mut self.dispatcher.storage);
        self.dispatcher.components.push(component);
    }
}

impl Add<'_, Config> {
    /// Adds a configuration value to the core's storage.
    pub fn config<C: Default + 'static>(&mut self, _config: C) {
        self.dispatcher.storage.add_config::<C>(C::default());
    }
}

impl Add<'_, Service> {
    /// Adds a service to the core's storage.
    pub fn service(&mut self, service: impl IntoService + 'static) {
        self.dispatcher.storage.add_service(service);
    }
}

pub struct ComponentDispatcher {
    components: Vec<Box<dyn patina::component::Component>>,
    storage: Storage,
}

impl Default for ComponentDispatcher {
    fn default() -> Self {
        Self::new()
    }
}

impl ComponentDispatcher {
    /// Creates a new locked ComponentDispatcher.
    pub const fn new_locked() -> TplMutex<Self> {
        TplMutex::new(efi::TPL_NOTIFY, Self::new(), "ComponentDispatcher")
    }

    /// Creates a new ComponentDispatcher.
    pub const fn new() -> Self {
        Self { components: Vec::new(), storage: Storage::new() }
    }

    /// Inserts a component at the given index. If no index is provided, the component is added to the end of the list.
    pub(crate) fn insert_component(&mut self, idx: usize, mut component: Box<dyn patina::component::Component>) {
        component.initialize(&mut self.storage);
        self.components.insert(idx, component);
    }

    /// Adds a service to storage.
    #[inline(always)]
    pub(crate) fn add_service<S: IntoService + 'static>(&mut self, service: S) {
        self.storage.add_service(service);
    }

    #[inline(always)]
    pub(crate) fn lock_configs(&mut self) {
        self.storage.lock_configs();
    }

    /// Sets the Boot Services table in storage.
    ///
    /// ## Safety
    ///
    /// The caller must ensure that the provided pointer will live for the lifetime of the DXE Core.
    #[inline(always)]
    pub(crate) unsafe fn set_boot_services(&mut self, mut bs: NonNull<efi::BootServices>) {
        unsafe {
            self.storage.set_boot_services(StandardBootServices::new(bs.as_mut()));
        }
    }

    /// Sets the Runtime Services table in storage.
    ///
    /// ## Safety
    ///
    /// The caller must ensure that the provided pointer will live for the lifetime of the DXE Core.
    #[inline(always)]
    pub(crate) unsafe fn set_runtime_services(&mut self, mut rs: NonNull<efi::RuntimeServices>) {
        unsafe {
            self.storage.set_runtime_services(StandardRuntimeServices::new(rs.as_mut()));
        }
    }

    /// Parses the HOB list producing a `Hob\<T\>` struct for each guided HOB found with a registered parser.
    pub(crate) fn insert_hobs(&mut self, hob_list: &HobList<'static>) {
        for hob in hob_list.iter() {
            if let patina::pi::hob::Hob::GuidHob(guid, data) = hob {
                let parser_funcs = self.storage.get_hob_parsers(&patina::OwnedGuid::from(guid.name));
                if parser_funcs.is_empty() {
                    let (f0, f1, f2, f3, f4, &[f5, f6, f7, f8, f9, f10]) = guid.name.as_fields();
                    let name = alloc::format!(
                        "{f0:08x}-{f1:04x}-{f2:04x}-{f3:02x}{f4:02x}-{f5:02x}{f6:02x}{f7:02x}{f8:02x}{f9:02x}{f10:02x}"
                    );
                    log::warn!(
                        "No parser registered for HOB: GuidHob {{ {:?}, name: Guid {{ {} }} }}",
                        guid.header,
                        name
                    );
                } else {
                    for parser_func in parser_funcs {
                        parser_func(data, &mut self.storage);
                    }
                }
            }
        }
    }

    /// Attempts to dispatch all components.
    ///
    /// This method will perform a single pass over all registered components, attempting to run each one.
    ///
    /// Returns `true` if at least one component was successfully dispatched, `false` otherwise.
    pub(crate) fn dispatch(&mut self) -> bool {
        let len = self.components.len();
        self.components.retain_mut(|component| {
            // Ok(true): Dispatchable and dispatched returning success
            // Ok(false): Not dispatchable at this time.
            // Err(e): Dispatchable and dispatched returning failure
            let name = component.metadata().name();
            log::trace!("Dispatch Start: Id = [{name:?}]");
            !match component.run(&mut self.storage) {
                Ok(true) => {
                    log::info!("Dispatched: Id = [{name:?}] Status = [Success]");
                    true
                }
                Ok(false) => false,
                Err(err) => {
                    log::error!("Dispatched: Id = [{name:?}] Status = [Failed] Error = [{err:?}]");
                    debug_assert!(false);
                    true // Component dispatched, even if it did fail, so remove from self.components to avoid re-dispatch.
                }
            }
        });
        len != self.components.len()
    }

    pub(crate) fn display_not_dispatched(&self) {
        if !self.components.is_empty() {
            let name_len = "name".len();
            let param_len = "failed_param".len();

            let max_name_len = self.components.iter().map(|c| c.metadata().name().len()).max().unwrap_or(name_len);
            let max_param_len = self
                .components
                .iter()
                .map(|c| c.metadata().failed_param().map(|s| s.len()).unwrap_or(0))
                .max()
                .unwrap_or(param_len);

            log::warn!("Components not dispatched:");
            log::warn!("{:-<max_name_len$} {:-<max_param_len$}", "", "");
            log::warn!("{:<max_name_len$} {:<max_param_len$}", "name", "failed_param");

            for component in &self.components {
                let metadata = component.metadata();
                log::warn!(
                    "{:<max_name_len$} {:<max_param_len$}",
                    metadata.name(),
                    metadata.failed_param().unwrap_or("")
                );
            }
        }
    }
}
