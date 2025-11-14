//! DXE Core
//!
//! A pure rust implementation of the UEFI DXE Core. Please review the getting started documentation at
//! <https://OpenDevicePartnership.github.io/patina/> for more information.
//!
//! ## Examples
//!
//! ```rust
//! # use core::ffi::c_void;
//! # use patina_dxe_core::*;
//! # #[derive(patina::component::IntoComponent, Default)]
//! # struct ExampleComponent;
//! # impl ExampleComponent {
//! #     fn entry_point(self) -> patina::error::Result<()> { Ok(()) }
//! # }
//! struct ExamplePlatform;
//!
//! impl ComponentInfo for ExamplePlatform {
//!   fn configs(mut add: Add<Config>) {
//!     add.config(32u32);
//!     add.config(true);
//!   }
//!
//!   fn components(mut add: Add<Component>) {
//!     add.component(ExampleComponent::default());
//!   }
//! }
//!
//! impl Platform for ExamplePlatform {
//!   type Extractor = patina_ffs_extractors::NullSectionExtractor;
//!   type ComponentInfo = Self;
//!
//!   fn prioritize_32_bit_memory() -> bool {
//!     true
//!   }
//!
//!   fn section_extractor() -> Self::Extractor {
//!     patina_ffs_extractors::NullSectionExtractor{}
//!   }
//! }
//!
//! static CORE: Core<ExamplePlatform> = Core::new();
//! ```
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
#![cfg_attr(all(not(feature = "std"), not(test)), no_std)]
#![feature(alloc_error_handler)]
#![feature(c_variadic)]
#![feature(allocator_api)]
#![feature(coverage_attribute)]

extern crate alloc;

mod allocator;
mod component_dispatcher;
mod config_tables;
mod cpu_arch_protocol;
mod decompress;
mod dispatcher;
mod driver_services;
mod dxe_services;
mod event_db;
mod events;
mod filesystems;
mod fv;
mod gcd;
#[cfg(all(target_os = "uefi", target_arch = "aarch64"))]
mod hw_interrupt_protocol;
mod image;
mod memory_attributes_protocol;
mod memory_manager;
mod misc_boot_services;
mod pecoff;
mod perf_timer;
mod protocol_db;
mod protocols;
mod runtime;
mod systemtables;
mod tpl_lock;

#[cfg(test)]
pub use component_dispatcher::MockComponentInfo;
pub use component_dispatcher::{Add, Component, ComponentInfo, Config, Service};

#[cfg(test)]
#[macro_use]
#[coverage(off)]
pub mod test_support;

use core::{
    ffi::c_void,
    ptr::{self, NonNull},
    str::FromStr,
};

use alloc::boxed::Box;
use gcd::SpinLockedGcd;
use memory_manager::CoreMemoryManager;
use mu_rust_helpers::{function, guid::CALLER_ID};
use patina::{
    component::IntoComponent,
    error::{self, Result},
    performance::{
        logging::{perf_function_begin, perf_function_end},
        measurement::create_performance_measurement,
    },
    pi::{
        hob::{HobList, get_c_hob_list_size},
        protocols::{bds, status_code},
        status_code::{EFI_PROGRESS_CODE, EFI_SOFTWARE_DXE_CORE, EFI_SW_DXE_CORE_PC_HANDOFF_TO_NEXT},
    },
};
use patina_ffs::section::SectionExtractor;
use patina_internal_cpu::{cpu::EfiCpu, interrupts::Interrupts};
use protocols::PROTOCOL_DB;
use r_efi::efi;

use crate::{
    component_dispatcher::ComponentDispatcher, config_tables::memory_attributes_table, perf_timer::PerfTimer,
    tpl_lock::TplMutex,
};

#[doc(hidden)]
#[macro_export]
macro_rules! ensure {
    ($condition:expr, $err:expr) => {{
        if !($condition) {
            error!($err);
        }
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! error {
    ($err:expr) => {{
        return Err($err.into()).into();
    }};
}

pub(crate) static GCD: SpinLockedGcd = SpinLockedGcd::new(Some(events::gcd_map_change));

/// A trait to be implemented by the platform to provide configuration values and types to be used directly by the
/// Patina DXE Core.
///
/// ## Example
///
/// ```rust
/// use patina_dxe_core::*;
///
/// struct ExamplePlatform;
///
/// impl Platform for ExamplePlatform {
///   type Extractor = patina_ffs_extractors::NullSectionExtractor;
///
///   type ComponentInfo = Self;
///
///   fn section_extractor() -> Self::Extractor {
///     patina_ffs_extractors::NullSectionExtractor{}
///   }
///
///   fn prioritize_32_bit_memory() -> bool {
///     true
///   }
/// }
///
/// impl ComponentInfo for ExamplePlatform {}
/// ```
#[cfg_attr(test, mockall::automock(type Extractor = patina_ffs_extractors::NullSectionExtractor; type ComponentInfo = MockComponentInfo;))]
pub trait Platform {
    /// The Platform component information type.
    type ComponentInfo: ComponentInfo;
    /// The platform's section extractor type, used when extracting sections from firmware volumes.
    type Extractor: SectionExtractor + 'static;
    /// Informs the core that it should prioritize allocating 32-bit memory when
    /// not otherwise specified.
    ///
    /// This should only be used as a workaround in environments where address width
    /// bugs exist in uncontrollable dependent software. For example, when booting
    /// to an OS that puts any addresses from UEFI into a uint32.
    fn prioritize_32_bit_memory() -> bool {
        false
    }

    /// Returns an instance of the platform's section extractor.
    fn section_extractor() -> Self::Extractor;

    /// Returns the performance timer frequency for the platform.
    ///
    /// By default, this returns `None`, indicating that the core should attempt to determine the frequency
    /// automatically using cpu architecture-specific methods.
    fn timer_frequency() -> Option<u64> {
        None
    }

    /// Informs the core of the GIC base addresses for AARCH64 systems.
    #[cfg(target_arch = "aarch64")]
    fn gic_bases() -> GicBases;
}

/// A configuration struct containing the GIC bases (gic_d, gic_r) for AARCH64 systems.
///
/// ## Example
///
/// ```rust
/// use patina_dxe_core::*;
///
/// struct PlatformConfig;
///
/// # impl ComponentInfo for PlatformConfig {}
///
/// impl Platform for PlatformConfig {
///   # type Extractor = patina_ffs_extractors::NullSectionExtractor;
///   # type ComponentInfo = Self;
///
///   # fn section_extractor() -> Self::Extractor {
///   #  patina_ffs_extractors::NullSectionExtractor{}
///   # }
///   # #[cfg(target_arch = "aarch64")]
///   fn gic_bases() -> GicBases {
///     GicBases::new(0x1E000000, 0x1E010000)
///   }
/// }
/// ```
#[derive(Debug, PartialEq)]
pub struct GicBases(pub u64, pub u64);

impl GicBases {
    /// Creates a new instance of the GicBases struct with the provided GIC Distributor and Redistributor base addresses.
    pub fn new(gicd_base: u64, gicr_base: u64) -> Self {
        GicBases(gicd_base, gicr_base)
    }
}

impl Default for GicBases {
    fn default() -> Self {
        panic!("GicBases `Config` must be manually initialized and registered with the Core using `with_config`.");
    }
}

/// Platform configured DXE Core responsible for the DXE phase of UEFI booting.
///
/// This struct is generic over two traits:
///
/// 1. [CoreConfig]: This trait exposes the platform-specific configuration options used directly by the DXE Core.
///    Associated types and methods within this trait provide configuration values that influence the behavior that may
///    be different between platforms, such as the prioritization of 32-bit memory allocations. It may also specify
///    associated types that define platform-specific implementations such as a SectionExtractor implementation.
/// 2. [Platform]: This trait provides callbacks for the platform to register additional patina components,
///    configurations and services that will be dispatched and made available during the DXE phase. These callbacks
///    will not influence core behavior directly, but allows the platform to attach dispatchable drivers and configure
///    them.
///
/// To properly use this struct, the platform must implement both the [CoreConfig] and [Platform] traits, then create
/// a static instance of the [Core] struct with the platform types as generic parameters (See example below). From
/// there, simply call the [entry_point](Core::entry_point) method within the main function to start the DXE Core.
///
/// ## Examples
///
/// ```rust
/// # use core::ffi::c_void;
/// # use patina_dxe_core::*;
/// # #[derive(patina::component::IntoComponent, Default)]
/// # struct ExampleComponent;
/// # impl ExampleComponent {
/// #     fn entry_point(self) -> patina::error::Result<()> { Ok(()) }
/// # }
/// struct ExamplePlatform;
///
/// impl ComponentInfo for ExamplePlatform {
///   fn configs(mut add: Add<Config>) {
///     add.config(32u32);
///     add.config(true);
///   }
///
///   fn components(mut add: Add<Component>) {
///     add.component(ExampleComponent::default());
///   }
/// }
///
/// impl Platform for ExamplePlatform {
///   type Extractor = patina_ffs_extractors::NullSectionExtractor;
///   type ComponentInfo = Self;
///
///   fn prioritize_32_bit_memory() -> bool {
///     true
///   }
///
///   fn section_extractor() -> Self::Extractor {
///     patina_ffs_extractors::NullSectionExtractor{}
///   }
/// }
///
/// static CORE: Core<ExamplePlatform> = Core::new();
/// ```
pub struct Core<P: Platform> {
    hob_list: TplMutex<HobList<'static>>,
    component_dispatcher: TplMutex<ComponentDispatcher>,
    _marker: core::marker::PhantomData<P>,
}

unsafe impl<P: Platform> Sync for Core<P> {}

impl<P: Platform> Default for Core<P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P: Platform> Core<P> {
    /// Creates a new instance of the DXE Core in the NoAlloc phase.
    pub const fn new() -> Self {
        Self {
            component_dispatcher: ComponentDispatcher::new_locked(),
            hob_list: TplMutex::new(efi::TPL_NOTIFY, HobList::new(), "HobList"),
            _marker: core::marker::PhantomData,
        }
    }

    /// The entry point for the Patina DXE Core.
    pub fn entry_point(&'static self, physical_hob_list: *const c_void) -> ! {
        self.init_memory(physical_hob_list);

        if let Err(err) = self.start(physical_hob_list) {
            log::error!("DXE Core failed to start: {err:?}");
        }

        loop {
            call_bds();
            log::info!("Returned from BDS phase. Re-dispatching.");
            if let Err(err) = self.core_dispatcher() {
                log::error!("DXE Core failed to re-dispatch: {err:?}");
            }
        }
    }

    /// Initializes the core with the given configuration, including GCD initialization, enabling allocations.
    pub fn init_memory(&self, physical_hob_list: *const c_void) {
        log::info!("DXE Core Crate v{}", env!("CARGO_PKG_VERSION"));

        GCD.prioritize_32_bit_memory(P::prioritize_32_bit_memory());

        let mut cpu = EfiCpu::default();
        cpu.initialize().expect("Failed to initialize CPU!");
        let mut interrupt_manager = Interrupts::default();
        interrupt_manager.initialize().expect("Failed to initialize Interrupts!");

        // For early debugging, the "no_alloc" feature must be enabled in the debugger crate.
        // patina_debugger::initialize(&mut interrupt_manager);

        if physical_hob_list.is_null() {
            panic!("HOB list pointer is null!");
        }

        gcd::init_gcd(physical_hob_list);

        log::trace!("Initial GCD:\n{GCD}");

        // After this point Rust Heap usage is permitted (since GCD is initialized with a single known-free region).
        // Relocate the hobs from the input list pointer into a Vec.
        self.hob_list.lock().discover_hobs(physical_hob_list);

        log::trace!("HOB list discovered is:");
        log::trace!("{:#x?}", self.hob_list);

        //make sure that well-known handles exist.
        PROTOCOL_DB.init_protocol_db();
        // Initialize full allocation support.
        allocator::init_memory_support(&self.hob_list.lock());
        // we have to relocate HOBs after memory services are initialized as we are going to allocate memory and
        // the initial free memory may not be enough to contain the HOB list. We need to relocate the HOBs because
        // the initial HOB list is not in mapped memory as passed from pre-DXE.
        self.hob_list.lock().relocate_hobs();

        // Add custom monitor commands to the debugger before initializing so that
        // they are available in the initial breakpoint.
        patina_debugger::add_monitor_command("gcd", "Prints the GCD", |_, out| {
            let _ = write!(out, "GCD -\n{GCD}");
        });

        // Initialize the debugger if it is enabled.
        patina_debugger::initialize(&mut interrupt_manager);

        log::info!("GCD - After memory init:\n{GCD}");

        self.component_dispatcher.lock().add_service(cpu);
        self.component_dispatcher.lock().add_service(interrupt_manager);
        self.component_dispatcher.lock().add_service(CoreMemoryManager);
        self.component_dispatcher.lock().add_service(PerfTimer::with_frequency(P::timer_frequency().unwrap_or(0)));
    }

    /// Performs a combined dispatch of Patina components and UEFI drivers.
    ///
    /// This function will continue to loop and perform dispatching until no components have been dispatched in a full
    /// iteration. The dispatching process involves a loop of two distinct dispatch phases:
    ///
    /// 1. A single iteration of dispatching Patina components, retaining those that were not dispatched.
    /// 2. A single iteration of dispatching UEFI drivers via the dispatcher module.
    fn core_dispatcher(&self) -> Result<()> {
        perf_function_begin(function!(), &CALLER_ID, create_performance_measurement);
        loop {
            // Patina component dispatch
            let dispatched = self.component_dispatcher.lock().dispatch();

            // UEFI driver dispatch
            let dispatched = dispatched
                || dispatcher::dispatch().inspect_err(|err| log::error!("UEFI Driver Dispatch error: {err:?}"))?;

            if !dispatched {
                break;
            }
        }
        perf_function_end(function!(), &CALLER_ID, create_performance_measurement);

        Ok(())
    }

    /// Returns the length of the HOB list.
    /// Clippy gets unhappy if we call get_c_hob_list_size directly, because it gets confused, thinking
    /// get_c_hob_list_size is not marked unsafe, but it is
    fn get_hob_list_len(hob_list: *const c_void) -> usize {
        unsafe { get_c_hob_list_size(hob_list) }
    }

    fn initialize_system_table(&self, physical_hob_list: *const c_void) -> Result<()> {
        let hob_list_slice = unsafe {
            core::slice::from_raw_parts(physical_hob_list as *const u8, Self::get_hob_list_len(physical_hob_list))
        };
        let relocated_c_hob_list = hob_list_slice.to_vec().into_boxed_slice();

        // Instantiate system table.
        systemtables::init_system_table();
        {
            let mut st = systemtables::SYSTEM_TABLE.lock();
            let st = st.as_mut().expect("System Table not initialized!");

            allocator::install_memory_services(st.boot_services_mut());
            gcd::init_paging(&self.hob_list.lock());
            events::init_events_support(st.boot_services_mut());
            protocols::init_protocol_support(st.boot_services_mut());
            misc_boot_services::init_misc_boot_services_support(st.boot_services_mut());
            config_tables::init_config_tables_support(st.boot_services_mut());
            runtime::init_runtime_support(st.runtime_services_mut());
            image::init_image_support(&self.hob_list.lock(), st);
            dispatcher::init_dispatcher();
            dxe_services::init_dxe_services(st);
            driver_services::init_driver_services(st.boot_services_mut());

            memory_attributes_protocol::install_memory_attributes_protocol();

            // re-checksum the system tables after above initialization.
            st.checksum_all();

            // Install HobList configuration table
            let (a, b, c, &[d0, d1, d2, d3, d4, d5, d6, d7]) =
                uuid::Uuid::from_str("7739F24C-93D7-11D4-9A3A-0090273FC14D").expect("Invalid UUID format.").as_fields();
            let hob_list_guid: efi::Guid = efi::Guid::from_fields(a, b, c, d0, d1, &[d2, d3, d4, d5, d6, d7]);

            config_tables::core_install_configuration_table(
                hob_list_guid,
                Box::leak(relocated_c_hob_list).as_mut_ptr() as *mut c_void,
                st,
            )
            .expect("Unable to create configuration table due to invalid table entry.");

            // Install Memory Type Info configuration table.
            allocator::install_memory_type_info_table(st).expect("Unable to create Memory Type Info Table");
        }

        let boot_services_ptr;
        let runtime_services_ptr;
        {
            let mut st = systemtables::SYSTEM_TABLE.lock();
            let st = st.as_mut().expect("System Table is not initialized!");
            boot_services_ptr = st.boot_services_mut() as *mut efi::BootServices;
            runtime_services_ptr = st.runtime_services_mut() as *mut efi::RuntimeServices;
        }

        tpl_lock::init_boot_services(boot_services_ptr);

        memory_attributes_table::init_memory_attributes_table_support();

        // Add Boot Services and Runtime Services to storage.
        // SAFETY: The pointers are a valid Boot Services and Runtime Services table pointers that live for the lifetime of the DXE Core.
        unsafe {
            self.component_dispatcher.lock().set_boot_services(NonNull::new_unchecked(boot_services_ptr));
            self.component_dispatcher.lock().set_runtime_services(NonNull::new_unchecked(runtime_services_ptr));
        }

        Ok(())
    }

    /// Registers platform provided components, configurations, and services.
    fn add_platform_components(&self) {
        let mut dispatcher = self.component_dispatcher.lock();

        P::ComponentInfo::components(Add::new(&mut dispatcher));

        P::ComponentInfo::configs(Add::new(&mut dispatcher));

        P::ComponentInfo::services(Add::new(&mut dispatcher));
    }

    /// Registers core provided components
    #[allow(clippy::default_constructed_unit_structs)]
    fn add_core_components(&self) {
        let mut dispatcher = self.component_dispatcher.lock();
        dispatcher.insert_component(0, decompress::DecompressProtocolInstaller::default().into_component());
        dispatcher.insert_component(0, systemtables::SystemTableChecksumInstaller::default().into_component());
        dispatcher.insert_component(0, cpu_arch_protocol::CpuArchProtocolInstaller::default().into_component());
        #[cfg(all(target_os = "uefi", target_arch = "aarch64"))]
        dispatcher.insert_component(
            0,
            hw_interrupt_protocol::HwInterruptProtocolInstaller::new(P::gic_bases()).into_component(),
        );
    }

    /// Starts the core, dispatching all drivers.
    pub fn start(&self, physical_hob_list: *const c_void) -> Result<()> {
        log::info!("Registering platform components");
        self.add_platform_components();
        log::info!("Finished.");

        log::info!("Registering default components");
        self.add_core_components();
        log::info!("Finished.");

        log::info!("Initializing System Table");
        self.initialize_system_table(physical_hob_list)?;
        log::info!("Finished.");

        log::info!("Parsing HOB list for Guided HOBs.");
        self.component_dispatcher.lock().insert_hobs(&self.hob_list.lock());
        log::info!("Finished.");

        let extractor = Box::leak(Box::new(P::section_extractor()));
        dispatcher::register_section_extractor(extractor);
        fv::register_section_extractor(extractor);

        log::info!("Parsing FVs from FV HOBs");
        fv::parse_hob_fvs(&self.hob_list.lock())?;
        log::info!("Finished.");

        log::info!("Dispatching Drivers");
        self.core_dispatcher()?;
        self.component_dispatcher.lock().lock_configs();
        self.core_dispatcher()?;
        log::info!("Finished Dispatching Drivers");

        self.component_dispatcher.lock().display_not_dispatched();

        core_display_missing_arch_protocols();

        dispatcher::display_discovered_not_dispatched();

        Ok(())
    }
}

const ARCH_PROTOCOLS: &[(uuid::Uuid, &str)] = &[
    (uuid::uuid!("a46423e3-4617-49f1-b9ff-d1bfa9115839"), "Security"),
    (uuid::uuid!("26baccb1-6f42-11d4-bce7-0080c73c8881"), "Cpu"),
    (uuid::uuid!("26baccb2-6f42-11d4-bce7-0080c73c8881"), "Metronome"),
    (uuid::uuid!("26baccb3-6f42-11d4-bce7-0080c73c8881"), "Timer"),
    (uuid::uuid!("665e3ff6-46cc-11d4-9a38-0090273fc14d"), "Bds"),
    (uuid::uuid!("665e3ff5-46cc-11d4-9a38-0090273fc14d"), "Watchdog"),
    (uuid::uuid!("b7dfb4e1-052f-449f-87be-9818fc91b733"), "Runtime"),
    (uuid::uuid!("1e5668e2-8481-11d4-bcf1-0080c73c8881"), "Variable"),
    (uuid::uuid!("6441f818-6362-4e44-b570-7dba31dd2453"), "Variable Write"),
    (uuid::uuid!("5053697e-2cbc-4819-90d9-0580deee5754"), "Capsule"),
    (uuid::uuid!("1da97072-bddc-4b30-99f1-72a0b56fff2a"), "Monotonic Counter"),
    (uuid::uuid!("27cfac88-46cc-11d4-9a38-0090273fc14d"), "Reset"),
    (uuid::uuid!("27cfac87-46cc-11d4-9a38-0090273fc14d"), "Real Time Clock"),
];

fn core_display_missing_arch_protocols() {
    for (uuid, name) in ARCH_PROTOCOLS {
        let guid = efi::Guid::from_bytes(&uuid.to_bytes_le());
        if protocols::PROTOCOL_DB.locate_protocol(guid).is_err() {
            log::warn!("Missing architectural protocol: {uuid:?}, {name:?}");
        }
    }
}

fn call_bds() {
    // Enable status code capability in Firmware Performance DXE.
    match protocols::PROTOCOL_DB.locate_protocol(status_code::PROTOCOL_GUID) {
        Ok(status_code_ptr) => {
            let status_code_protocol = unsafe { (status_code_ptr as *mut status_code::Protocol).as_mut() }.unwrap();
            (status_code_protocol.report_status_code)(
                EFI_PROGRESS_CODE,
                EFI_SOFTWARE_DXE_CORE | EFI_SW_DXE_CORE_PC_HANDOFF_TO_NEXT,
                0,
                &patina::guids::DXE_CORE,
                ptr::null(),
            );
        }
        Err(err) => log::error!("Unable to locate status code runtime protocol: {err:?}"),
    };

    if let Ok(protocol) = protocols::PROTOCOL_DB.locate_protocol(bds::PROTOCOL_GUID) {
        let bds = protocol as *mut bds::Protocol;
        unsafe {
            // If bds entry returns: then the dispatcher must be invoked again,
            // if it never returns: then an operating system or a system utility have been invoked.
            ((*bds).entry)(bds);
        }
    }
}
