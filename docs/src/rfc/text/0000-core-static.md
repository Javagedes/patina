# RFC: `Static Resolution and usage in the Core`

This RFC proposes multiple architectural changes to our current usage of `static` throughout the codebase and with the
core including both legitimate `static` usage consolidation and static polymorphism where possible rather than dynamic
polymorphism.

## Change Log

- 2025-11-10: Initial RFC created.
- 2025-11-11: Clarified that this change reduces the initial stack frame size by sacrificing some binary size.
- 2025-11-11: Clarified that the performance gains are a side affect, not the intent of this change and that the
  performance differences would be incredibly small, at least for the impacted code today.
- 2025-11-11: Added test performance impact as tests can remove the global lock, and run in parallel.
- 2025-11-11: Remove associated constant from Platform trait to allow usage of `mockall::automock`
- 2025-11-11: Specify that not all statics will necessarily go in `UefiState` struct. Specify that the intent is to
  better organize the fields inside of the core, instead of having a core with 30 fields.

## Motivation

1. Reduction of stack size
2. Testing improvements for Patina maintainers
3. Improved code cleanliness for Patina maintaineres
4. Clear interface for Platform implementors on configuration options

## Technology Background

The technological background required for this RFC is entirely related to the rust programming language itself. Of
this, the prime knowledge area is rust traits, generics, and the static polymorphism provided by the traits.

It is suggested you read:

1. [rust-lang: Traits](https://doc.rust-lang.org/reference/items/traits.html)
2. [nomicon: repr-rust](https://doc.rust-lang.org/nomicon/repr-rust.html)

## Goals

1. Reduction of stack size
   1. Static definition of the Core reduces initial stack frame size
   2. Deferred instantiation of components reduces initial stack frame size

2. Testing improvements for Patina maintainers
   1. Removal of statics reduces complexity writing tests that are properly reset
   2. Generics for Core dependencies allows for easier mocking
   3. Improved testing performance

3. Improved code cleanliness for Patina maintaineres
   1. Never calling "efiapi" functions
   2. Making "efiapi" functions a light wrapper around pure-rust implementations

4. Clear Platform Interface and Configuration
   1. Clearly describes all configurations available to the platform.
   2. Clear platform notification when platform configuration options change.

## Requirements

1. Stack size / performance improvements*
    1. Platforms will declare the `Core` as a static in their binary file
    2. Platforms will declare their `Core` generics via the `Platform` trait (described in (4))
    3. Component, Service, and Config instantiation is moved to a `Platform` trait method, and thus does not take
       up space on the initial stack frame.
    4. Current usage of dynamic polymorphism in statics be switched to static polymorphism (e.g. section_extractor in
       the dispatcher context)*

2. Testing improvements for Patina maintainers
    1. All statics are moved into the `UefiState` field of the `Core`. e.g. `SpinLockedGcd`, `DispatcherContext`, etc.
    2. Possibility to add generics at additional levels, to make mocking for tests simple
    3. Ignore code coverage for all "efiapi" functions
    4. Removal of global lock, allowing for more parallel testing.

3. Improved code cleanliness for Patina maintaineres
    1. All pure-rust methods directly access `UefiState` field in the `Core`. e.g. `self.uefi_state.<thing>`.
    2. A `instance` function in the core provides an abstracted interface for accessing the `Core` statically in
       "efiapi" functions
    3. Only "efiapi" functions will use the `instance` functions
    4. "efiapi" functions are only wrappers around a static-less `Core` function accessed via `instance` function.
    5. "efiapi" functions are only for usage in the system tables or event notify callbacks. They are not to be called
       directly by other rust code.

4. Clear Platform Interface and Configuration
    1. A `Platform` trait is defined, which uses trait `type` functionality to clearly specify generics
       e.g. `type Extractor: SectionExtractor`
    2. The `Platform` trait uses static trait functions to specify platform configurations that is not "const init-able"
       such as something that requires an allocation
    3. `const` values for setting configurations that can be created at compile-time
    4. The Platform trait itself will remain stateless.

\* While performance improvements are mentioned here, they are only a side affect of the change and not the intent of
   of the change. By switching to static trait resolution at compile time (static polymorphism) rather then dynamic
   polymorphism at runtime, we save some performance on vtable function pointer indirection. Unless the code is
   incredibly "hot", the performance improvements will **not** be noticeable. As it stands, none of the dyn trait
   objects impacted by the change are "hot" enough code for performance to be impacted, though that does not mean
   future additions won't be.

## Unresolved Questions

- How to handle components like the advanced logger that need the hob list. Maybe provide the hob list in the
  `components` function?

## Prior Art (Existing PI C Implementation)

Previous to this RFC, static state is spread across the entire repository, and platforms currently registered configuration
for the core via dynamic polymorphism.

## Alternatives

N/A, keep the same.

## Rust Code Design

### Addition of the `Platform` trait

The first design change is that we will introduce a `Platform` trait that will fully describe all platform
customizations available. This includes both function implementations for configuration, and type specifications for
generic trait resolution. If you remember previously, we did this in the core itself, and it lead to a laundry list of
traits with complex types specified. This interface is cleaner, and provides less complexities in the `Core`.

To start, this trait will have a limited number of configuration options as shown below, but it is expected that more
will be specified as needed. Note that this trait is now what adds components / configs / services, instead of the core.

**Note:** It is elected **not** to use associated consts (e.g. const fields) in the Platform trait as `automock` does not
mocking traits that use const fields without defaults. This can be re-evaluated at a different time if need be.

```rust
// In patina_dxe_core/src/lib.rs
#[cfg_attr(test, mockall::automock)]
trait Platform {
    type Extractor: SectionExtractor;

    fn prioritize_32_bit_memory() -> bool { false }

    fn section_extractor() -> Self::SectionExtractor;

    fn components(add: &mut Add<Component>) { }

    fn configs(add: &mut Add<Config>) {  }

    fn services(add: &mut Add<Service>) {  }

    #[cfg(target_arch = "aarch64")]
    fn gic_bases() -> GicBases;
}
```

This will introduce changes to the core and how it consumes the trait. An example is shown below

```rust
pub struct Core<P: Platform> {
    ...
    _p: PhantomData<P>
}

impl <P: Platform> Core<P> {
    /// This was originally `init_memory`. It is now `start` and the only public function.
    pub fn start(mut self, physical_hob_list: *const c_void) -> ! {
        ...

        GCD.prioritize_32_bit_memory(P::prioritize_32_bit_memory());

        ...
    }

    // This was originally `start`. It is now a method (probably not dispatch) called by `start` above.
    fn dispatch(&mut self) -> Result<()> {
        ...

        Self::register_section_extractor(P::section_extractor());

        ...
    }
}
```

### Creation of the `UefiState` struct

Since we will be moving all of the static state into the Core, we need a clean way to store all of this state. To do
that, we will create a new struct called `UefiState` to store some of the UEFI related statics (Such as the dispatcher
context, etc.). Other statics that are more "Kernel-like" in nature will be moved either to a new structure or into the
Core itself. The decision on where to put each individual static is an implementation detail and will not be decided in
this RFC. The intent is to specify that we will purposefully organize the statics inside the core instead of having all
statics sit in the top-level Core struct as fields.

Please note that to reduce the complexity of the PR implementing this RFC, moving things into the Core and away from
being `static` will happen over multiple PRs. The first one we will do is the dispatcher context, so the example below
will show the dispatcher context being moved into `UefiState`

Another benefit with this layout is that some of the dyn trait objects currently used in statics (because we cannot
know the type at compile time) can now be converted to static polymorphism because it is all handled by the types
specified in the `Platform` trait.

```rust
// in lib.rs
struct UefiState<P: Platform> {
    dispatcher_context: TplMutex<DispatcherContext<P::Extractor>>,
    ...
}

struct Core<P: Platform> {
    ...
    uefi_state: UefiState<P>,
}
```

### Creation of Atomic Pointer to the Core

The biggest limitation of the Core is that we are compatible with "efiapi" functions, however these functions cross
the FFI boundary and thus we cannot capture state in lambdas, like is the normal process for getting Sync/Send safe
data into callbacks. To get around this, we will create a static pointer that holds a reference to our Core, and will
produce an API interface for accessing this state.

The next limitation with this process is that we have a `Core` struct with a generic `P` for the platform. Due to this
the layout of the `Core` is not stable and we cannot safely convert to the `Core` without also knowing `P`. What this
means is that we must move all "efiapi" functions into the `Core`, which allows static polymorphism to handle knowing
what `P` is for us (e.g. we can just do `Self::instance()`).

```rust
/// in lib.rs
static __SELF: AtomicPtr<u8> = AtomicPtr::new(core::ptr::null_mut());

impl <P: Platform> Core {
    fn set_instance(&'static self) {
        let ptr = NonNull::from(self).cast::<u8>().as_ptr();
        __SELF.store(ptr, core::sync::atomic::Ordering::SeqCst);
    }

    pub(crate) fn instance<'a>() -> &'a Self {
        let ptr = __SELF.load(core::sync::atomic::Ordering::SeqCst);
        unsafe {
            NonNull::new(ptr).expect("Core instance is already initialize")
                .cast::<Self>()
                .as_ref()
        }
    }
    pub fn init_memory(&'static self, physical_hob_list: *const c_void) -> &'static self {
        self.set_instance();

        ...
    }
}
```

The next final tidbit which is handy for this implementation is that `impl`'s of a struct do not have to be in the same
module that the struct is defined. This allows us to scatter `Core<P>` impls throughout the workspace.

A short and sweet example of how we will implement efiapi functions across the workspace is seen below:

```rust
impl <P: Platform> Core {
    pub(crate) fn trust(handle: efi::Handle, file: &efi::Guid) -> Result<(), EfiError> {
        let dispatcher = self.uefi_state.dispatcher_context.lock();
        for driver in dispatcher.pending_drivers.iter_mut() {
            if driver.firmware_volume_handle == handle && OrdGuid(driver.file_name) == OrdGuid(*file) {
                driver.security_status = efi::Status::SUCCESS;
                return Ok(());
            }
        }
        Err(EfiError::NotFound)
    }

    extern "efiapi" fn trust_efiapi(firmware_volume_handle: efi::Handle, file_name: *const efi::Guid) -> efi::Status {
        if file_name.is_null() {
            return efi::Status::INVALID_PARAMETER;
        }

        let file_name = unsafe { file_name.read_unaligned() };

        match Self::instance().trust(firmware_volume_handle, &file_name) {
            Err(status) => status.into(),
            Ok(_) => efi::Status::SUCCESS,
        }
    }

    fn init_dxe_services(system_table: &mut EfiSystemTable) {
        ...
        trust: Self::trust_efiapi,
    }
}
```

### Platform Interface changes

We've now seen all of the core changes. What does the the change look for the platform? The platform now manually
implements the `Platform` trait. Pretty much all platform config has moved there. That is about it. Lets see the
example:

```rust
struct Platform;

impl patina::Platform for Platform {
    const PRIORITIZE_32_BIT_MEMORY: bool = false;

    type Extractor: SectionExtractor = CompositeSectionExtractor;

    fn section_extractor -> Self::Extractor { CompositeSectionExtractor::default() }

    fn components(add: &mut Add<Component>) {
        add.add_component(...);
        add.add_component(...);
    }

    fn configs(add: &mut Add<Config>) {
        add.add_config(...);
    }

    fn services(c: &mut Add<Service>) {
        add.add_service(...);
    }
}

static CORE: Core<Platform> = Core::new();

pub extern "efiapi" fn _start(physical_hob_list: *const c_void) -> ! {
    ...
    CORE.start(physical_hob_list)
}
```

## Guide-Level Explanation

In this RFC, we are attempting to clean up and consolidate the static usage in the `patina_dxe_core` crate, which has
many benefits to both patina developers and platform owners. For Patina developers, by consolidating all static usage
into the `Core` struct, it allows us to much more easily test our code because we do not have to worry about some
static state being affected by other tests. This also allows us to easily specify generics in more locations throughout
the codebase, which enables easier testing because we can mock parts that we are not actually testing, but must exist
to compile.

For platform owners, static polymorphism allows them to fully define all of their platform configurations and
dependencies at compile time, which will result in compilation errors when initially configuring the core for their
platform, or as configurations evolve with Patina.

Generically, the combination of both a static core and delayed instantiation of components should reduce the size of
the initial stack frame. While the size of the initial stack frame is not currently a concern, as platforms begin to
use more patina components, it will be. This change will increase the binary size (size of the `Core` object) to
reduce the initial stack frame size (size of `Core` + `Config`'s + `Component`'s).

In a STD compilation, it was seen that the initial stack frame was reduced from 568 to 488 with this change (with no
registered components, configs, or services). Adding components, configs, or services increased the initial stack size
of the pre-rfc implementation by the size of the object + minimal overhead where as with this implementation, almost
no additional stack frame size was seen.

Additionally, I will note that there will be a very (and I mean very) slight
performance increase as we certain functionalities (such as the section extractor) move away from dyn trait objects
and vtable indirection. I want to reiterate that this is incredibly small performance gain. Almost worth not
mentioning, but I do find it important to at least mention in writing.
