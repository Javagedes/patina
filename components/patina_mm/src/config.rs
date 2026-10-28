//! Management Mode (MM) Configuration
//!
//! Defines the configuration necessary for the MM environment to be initialized and used by components
//! dependent on MM details.
//!
//! ## MM Configuration Usage
//!
//! It is expected that the MM configuration will be initialized by the environment that registers services for the
//! platform. The configuration can have platform-fixed values assigned during its initialization. It should be common
//! for at least the communication buffers to be populated as a mutable configuration during boot time. It is
//! recommended for a "MM Configuration" component to handle all MM configuration details with minimal other MM related
//! dependencies and lock the configuration so it is available for components that depend on the immutable configuration
//! to perform MM operations.
//!
//! ## License
//!
//! Copyright (C) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use alloc::{sync::Arc, vec::Vec};
use core::{fmt, pin::Pin};

use patina::{
    BinaryGuid, Guid, UEFI_PAGE_MASK,
    component::service::{Service, uefi_services::tpl::TplServices},
    management_mode::MmCommBufferStatus,
    pi::protocol::communication::EfiMmCommunicateHeader,
    uefi::{
        boot_services::tpl::Tpl,
        tpl_mutex::{TplMutex, TplMutexGuard},
    },
    writelncrlf,
};

/// Management Mode (MM) Configuration
///
/// A standardized configuration structure for MM components to use when initializing and using MM services.
#[derive(Debug, Clone)]
pub struct MmCommunicationConfiguration {
    /// ACPI base address used to access the ACPI Fixed hardware register set.
    pub acpi_base: AcpiBase,
    /// MMI Port for sending commands to the MM handler.
    pub cmd_port: MmiPort,
    /// MMI Port for receiving data from the MM handler.
    pub data_port: MmiPort,
    /// List of Management Mode (MM) Communicate Buffers
    pub comm_buffers: Vec<CommunicateBuffer>,
    /// Enable runtime buffer updates (currently via the MM Communication Buffer Update Protocol).
    /// When enabled, the communicator will register a protocol notify to update
    /// the buffer specified by `updatable_buffer_id`.
    pub enable_comm_buffer_updates: bool,
    /// Buffer ID to update when MM Communication Buffer Update Protocol is installed.
    /// Only used when `enable_comm_buffer_updates` is true.
    /// If None when updates are enabled, no buffer will be updated.
    pub updatable_buffer_id: Option<u8>,
}

impl Default for MmCommunicationConfiguration {
    fn default() -> Self {
        MmCommunicationConfiguration {
            acpi_base: AcpiBase::Mmio(0),
            cmd_port: MmiPort::Smi(0xFF),
            data_port: MmiPort::Smi(0x00),
            comm_buffers: Vec::new(),
            enable_comm_buffer_updates: false,
            updatable_buffer_id: None,
        }
    }
}

impl fmt::Display for MmCommunicationConfiguration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writelncrlf!(f, "MM Communication Configuration:")?;
        writelncrlf!(f, "  ACPI Base: {}", self.acpi_base)?;
        writelncrlf!(f, "  Command Port: {}", self.cmd_port)?;
        writelncrlf!(f, "  Data Port: {}", self.data_port)?;
        writelncrlf!(f, "  Communication Buffers ({}):", self.comm_buffers.len())?;

        if self.comm_buffers.is_empty() {
            writelncrlf!(f, "    <none>")
        } else {
            for buffer in &self.comm_buffers {
                match buffer.try_lock() {
                    Ok(mut access) => writelncrlf!(
                        f,
                        "    Buffer {:#04X}: ptr={:p}, len=0x{:X}",
                        buffer.id(),
                        access.as_ptr(),
                        access.len(),
                    )?,
                    Err(_) => writelncrlf!(f, "    Buffer {:#04X}: busy", buffer.id())?,
                }
            }
            Ok(())
        }
    }
}

/// MM Communicator Service Status Codes
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum CommunicateBufferStatus {
    /// Another alias is already accessing this buffer.
    Busy,
    /// The buffer is too small to hold the header.
    TooSmallForHeader,
    /// The buffer is too small to hold the message.
    TooSmallForMessage,
    /// A valid recipient GUID was not provided.
    InvalidRecipient,
    /// A comm buffer was not provided (null pointer).
    NoBuffer,
    /// The does not meet the alignment requirements.
    NotAligned,
    /// Buffer creation failed due to address space validation errors.
    AddressValidationFailed,
}

/// Management Mode (MM) Communicate Buffer
///
/// Exclusive access to communication RAM, mailbox, and tracked message state.
///
/// Obtained from [`CommunicateBuffer::try_lock`]. Borrowed data cannot outlive
/// the transaction guard. This type cannot be cloned.
pub struct CommunicateBufferAccess {
    /// Pointer to the buffer in memory.
    buffer: &'static mut [u8],
    /// ID of the buffer.
    id: u8,
    /// Length of the total buffer in bytes.
    length: usize,
    /// Handler GUID tracked independently to check against comm buffer contents
    private_recipient: Option<patina::BinaryGuid>,
    /// Message length tracked independently to check against comm buffer contents
    private_message_length: usize,
    /// Whether this buffer is enabled and should be used for communication.
    /// Disabled buffers are skipped when searching for buffers by ID.
    enabled: bool,
    /// Pointer to the MM communication buffer status mailbox structure.
    /// This is used to communicate status between DXE and MM environments.
    /// If None, this is a buffer without mailbox status support.
    status_mailbox: Option<&'static mut MmCommBufferStatus>,
}

/// A shared communication buffer. Clones share both memory and transaction state.
///
/// Hold [`Self::try_lock`] throughout a complete request, MM execution, and response.
/// A competing or reentrant transaction fails rather than accessing aliased memory.
#[derive(Clone)]
pub struct CommunicateBuffer {
    inner: Arc<TplMutex<CommunicateBufferAccess, Service<dyn TplServices>>>,
    id: u8,
}

impl CommunicateBuffer {
    /// Takes exclusive ownership of normal RAM for a shared communication buffer.
    pub fn new(buffer: Pin<&'static mut [u8]>, id: u8, tpl: Service<dyn TplServices>) -> Self {
        Self::from_access(CommunicateBufferAccess::new(buffer, id), tpl)
    }

    fn from_access(access: CommunicateBufferAccess, tpl: Service<dyn TplServices>) -> Self {
        let id = access.id;
        Self { inner: Arc::new(TplMutex::new(tpl, Tpl::NOTIFY, access)), id }
    }

    /// Creates a shared buffer from an exclusively owned firmware RAM region.
    ///
    /// # Safety
    /// The region must be valid, writable, static normal RAM, not MMIO, and must
    /// remain exclusively owned by this handle and its clones. MM may access it
    /// only synchronously during execution while the transaction guard is held.
    pub unsafe fn from_raw_parts(
        buffer: *mut u8,
        size: usize,
        id: u8,
        tpl: Service<dyn TplServices>,
    ) -> Result<Self, CommunicateBufferStatus> {
        // SAFETY: The caller transfers exclusive ownership of the region.
        let access = unsafe { CommunicateBufferAccess::from_raw_parts(buffer, size, id)? };
        Ok(Self::from_access(access, tpl))
    }

    /// Creates a shared buffer and optional mailbox from firmware normal RAM.
    ///
    /// # Safety
    /// The buffer and mailbox must be valid, writable, static, nonoverlapping
    /// normal RAM exclusively owned by this handle and its clones. MM accesses
    /// must occur only synchronously while the transaction guard is held.
    pub unsafe fn from_firmware_region(
        address: u64,
        size_bytes: usize,
        buffer_id: u8,
        status_mailbox_address: Option<u64>,
        tpl: Service<dyn TplServices>,
    ) -> Result<Self, CommunicateBufferStatus> {
        // SAFETY: The caller transfers exclusive ownership of both regions.
        let access = unsafe {
            CommunicateBufferAccess::from_firmware_region(address, size_bytes, buffer_id, status_mailbox_address)?
        };
        Ok(Self::from_access(access, tpl))
    }

    /// Acquires exclusive access to the buffer, mailbox, and tracked metadata.
    ///
    /// Returns [`CommunicateBufferStatus::Busy`] if any clone is in use.
    pub fn try_lock(
        &self,
    ) -> Result<TplMutexGuard<'_, CommunicateBufferAccess, Service<dyn TplServices>>, CommunicateBufferStatus> {
        self.inner.try_lock().map_err(|()| CommunicateBufferStatus::Busy)
    }

    /// Returns the immutable buffer ID.
    pub fn id(&self) -> u8 {
        self.id
    }
}

impl fmt::Debug for CommunicateBuffer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CommunicateBuffer").field("id", &self.id).finish_non_exhaustive()
    }
}

#[cfg(test)]
/// Creates TPL services for host tests exercising communication guards.
pub(crate) fn mock_tpl_service() -> Service<dyn TplServices> {
    use patina::component::service::uefi_services::tpl::{MockTplServices, PreviousTpl};
    let mut tpl = MockTplServices::new();
    tpl.expect_raise_tpl().returning(|_| PreviousTpl::from_raw(4));
    tpl.expect_restore_tpl().returning(|_| ());
    Service::mock(alloc::boxed::Box::new(tpl))
}

impl CommunicateBufferAccess {
    /// The minimum required buffer size to hold a communication header.
    const MINIMUM_BUFFER_SIZE: usize = EfiMmCommunicateHeader::size();

    /// The offset in the buffer where the message starts.
    const MESSAGE_START_OFFSET: usize = EfiMmCommunicateHeader::size();

    pub(crate) fn validate_firmware_region(
        address: u64,
        size: usize,
        mailbox: Option<u64>,
    ) -> Result<(), CommunicateBufferStatus> {
        let address = usize::try_from(address).map_err(|_| CommunicateBufferStatus::AddressValidationFailed)?;
        let end = address.checked_add(size).ok_or(CommunicateBufferStatus::AddressValidationFailed)?;
        if size < Self::MINIMUM_BUFFER_SIZE {
            return Err(CommunicateBufferStatus::TooSmallForHeader);
        }
        if address == 0 {
            return Err(CommunicateBufferStatus::NoBuffer);
        }
        if address & UEFI_PAGE_MASK != 0 {
            return Err(CommunicateBufferStatus::NotAligned);
        }
        if size > isize::MAX as usize {
            return Err(CommunicateBufferStatus::AddressValidationFailed);
        }
        if let Some(mailbox) = mailbox {
            let mailbox = usize::try_from(mailbox).map_err(|_| CommunicateBufferStatus::AddressValidationFailed)?;
            let mailbox_end = mailbox
                .checked_add(core::mem::size_of::<MmCommBufferStatus>())
                .ok_or(CommunicateBufferStatus::AddressValidationFailed)?;
            if mailbox == 0 || (mailbox < end && address < mailbox_end) {
                return Err(CommunicateBufferStatus::AddressValidationFailed);
            }
        }
        Ok(())
    }

    /// Replaces the region while retaining the transaction lock shared by every handle.
    ///
    /// # Safety
    /// New regions must satisfy `CommunicateBuffer::from_firmware_region`. An exact
    /// repeat of the current region is allowed and does not recreate references.
    pub(crate) unsafe fn replace_firmware_region(
        &mut self,
        address: u64,
        size: usize,
        mailbox: u64,
    ) -> Result<(), CommunicateBufferStatus> {
        Self::validate_firmware_region(address, size, Some(mailbox))?;
        let address = address as usize;
        let mailbox = mailbox as usize;
        let old_address = self.buffer.as_ptr() as usize;
        let old_mailbox = self.status_mailbox.as_deref().map(|status| core::ptr::from_ref(status) as usize);
        if address == old_address && size == self.length && old_mailbox == Some(mailbox) {
            self.enable();
            return Ok(());
        }

        let overlaps = |start: usize, length: usize| {
            (address < start + length && start < address + size)
                || (mailbox < start + length && start < mailbox + core::mem::size_of::<MmCommBufferStatus>())
        };
        if overlaps(old_address, self.length)
            || old_mailbox.is_some_and(|start| overlaps(start, core::mem::size_of::<MmCommBufferStatus>()))
        {
            return Err(CommunicateBufferStatus::AddressValidationFailed);
        }

        // SAFETY: The caller guarantees exclusive firmware RAM. Validation above
        // rules out overlap with the references still held by the current region.
        // The replacement stays behind this same lock, so no clone retains old references.
        *self = unsafe { Self::from_firmware_region(address as u64, size, self.id, Some(mailbox as u64))? };
        Ok(())
    }

    /// Creates a new `CommunicateBuffer` with the given buffer and ID.
    fn new(mut buffer: Pin<&'static mut [u8]>, id: u8) -> Self {
        let length = buffer.len();
        log::debug!(target: "mm_comm", "Creating new CommunicateBuffer: id={id}, size=0x{length:X}");
        buffer.fill(0);

        let ptr = Pin::into_inner(buffer);

        log::trace!(target: "mm_comm", "CommunicateBuffer {id} created successfully at address {:p}", ptr.as_ptr());
        Self {
            buffer: ptr,
            id,
            length,
            private_recipient: None,
            private_message_length: 0,
            enabled: true,
            status_mailbox: None,
        }
    }

    /// Returns a reference to the buffer as a slice of bytes.
    /// This is only used for internal operations.
    fn as_slice(&self) -> &[u8] {
        self.buffer
    }

    /// Returns a mutable reference to the buffer as a slice of bytes.
    /// This is only used for internal operations.
    fn as_slice_mut(&mut self) -> &mut [u8] {
        self.buffer
    }

    /// Creates a new `CommunicateBuffer` from a raw pointer and size.
    ///
    /// ## Safety
    ///
    /// - The buffer must be a valid pointer to a memory region of at least `size` bytes.
    /// - The buffer pointer must not be null.
    /// - The buffer must have a static lifetime.
    /// - The buffer must not be moved in memory while it is being used.
    /// - The buffer must not be used by any other code.
    /// - The buffer must be page (4k) aligned so paging attributes can be applied to it.
    /// - The buffer size must be sufficient to hold at least the MM communication header.
    unsafe fn from_raw_parts(buffer: *mut u8, size: usize, id: u8) -> Result<Self, CommunicateBufferStatus> {
        log::trace!(target: "mm_comm", "Creating CommunicateBuffer from raw parts: id={id}, ptr={buffer:p}, size=0x{size:X}");

        if let Err(error) = Self::validate_firmware_region(buffer as u64, size, None) {
            log::error!(target: "mm_comm", "Invalid buffer {id}: ptr={buffer:p}, size=0x{size:X}, error={error:?}");
            return Err(error);
        }

        log::debug!(target: "mm_comm", "CommunicateBuffer {id} validation passed, creating buffer");
        // SAFETY: Caller guarantees pointer validity per function safety contract
        unsafe { Ok(Self::new(Pin::new(core::slice::from_raw_parts_mut(buffer, size)), id)) }
    }

    /// Creates a `CommunicateBuffer` from a validated firmware-provided memory region.
    ///
    /// This is the recommended method for creating communicate buffers from HOB data or other
    /// firmware-provided memory regions.
    ///
    /// ## Parameters
    ///
    /// - `address` - Physical address of the communication buffer
    /// - `size_bytes` - Size of the buffer in bytes
    /// - `buffer_id` - Unique identifier for this buffer
    ///   - Can be used in future calls to refer to the buffer
    ///
    /// ## Returns
    ///
    /// - `Ok(CommunicateBuffer)` - Successfully created and validated buffer
    /// - `Err(CommunicateBufferStatus)` - Validation failed with specific error
    ///
    /// ## Safety
    ///
    /// The caller must ensure:
    /// - The memory region is valid and accessible throughout buffer lifetime
    /// - The memory is not used by other components concurrently
    /// - The firmware has guaranteed the memory region is stable and properly mapped
    /// - If provided, the `status_mailbox_address` points to a valid `MmCommBufferStatus` structure
    unsafe fn from_firmware_region(
        address: u64,
        size_bytes: usize,
        buffer_id: u8,
        status_mailbox_address: Option<u64>,
    ) -> Result<Self, CommunicateBufferStatus> {
        Self::validate_firmware_region(address, size_bytes, status_mailbox_address)?;
        // Check that the address provided is addressable on this system.
        // A 32-bit system will fail this if the address is over 4GB.
        let address = usize::try_from(address).map_err(|_| CommunicateBufferStatus::AddressValidationFailed)?;

        let ptr = address as *mut u8;

        log::info!(
            target: "mm_comm",
            "Creating CommunicateBuffer from firmware region: addr=0x{address:X}, size=0x{size_bytes:X}, id={buffer_id}"
        );

        let mailbox = if let Some(status_addr) = status_mailbox_address {
            let status_addr =
                usize::try_from(status_addr).map_err(|_| CommunicateBufferStatus::AddressValidationFailed)?;
            let status_ptr = status_addr as *mut MmCommBufferStatus;

            // SAFETY: Caller guarantees exclusive, static normal RAM. The mailbox
            // was checked for null, address overflow, and overlap with the buffer.
            Some(unsafe { &mut *status_ptr })
        } else {
            None
        };
        // SAFETY: Caller guarantees firmware memory region is valid and stable per the function safety contract.
        let mut buffer = unsafe { Self::from_raw_parts(ptr, size_bytes, buffer_id)? };
        buffer.status_mailbox = mailbox;
        if let Some(status_addr) = status_mailbox_address {
            log::info!(target: "mm_comm", "Buffer {buffer_id} status mailbox configured at address 0x{status_addr:X}");
        }

        Ok(buffer)
    }

    /// Returns the length of the buffer.
    pub fn len(&self) -> usize {
        self.length
    }

    /// Returns whether the buffer is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the ID of the buffer.
    pub fn id(&self) -> u8 {
        self.id
    }

    /// Returns whether this buffer is enabled for communication.
    pub fn is_enabled(&self) -> bool {
        self.enabled
    }

    /// Disables this buffer, preventing it from being used for communication.
    /// Disabled buffers are skipped when searching for buffers by ID.
    pub fn disable(&mut self) {
        log::debug!(target: "mm_comm", "Disabling comm buffer {}", self.id);
        self.enabled = false;
    }

    pub(crate) fn enable(&mut self) {
        self.enabled = true;
    }

    /// Returns a pointer to the underlying buffer memory.
    ///
    /// This method provides controlled access to the buffer pointer for operations
    /// that require direct memory access, such as registering with hardware or
    /// passing to external APIs.
    ///
    /// ## Safety Considerations
    ///
    /// While this method is safe to call, the returned pointer should be used
    /// with caution. The caller must ensure they do not:
    ///
    /// - Write beyond the buffer boundaries (use `len()` to check size)
    /// - Modify buffer contents without proper coordination with buffer state
    /// - Use the pointer after the buffer has been dropped
    pub fn as_ptr(&mut self) -> *mut u8 {
        self.buffer.as_mut_ptr()
    }

    /// Sets the communication buffer status to indicate a valid buffer before triggering MMI.
    ///
    /// This must be called before triggering the SW MMI to inform the MM core that
    /// the communication buffer contains valid data to process.
    ///
    /// ## Returns
    ///
    /// - `Ok(())` if the status was set successfully
    /// - `Err(CommunicateBufferStatus)` if this buffer has no status mailbox configured
    pub fn set_comm_buffer_valid(&mut self) -> Result<(), CommunicateBufferStatus> {
        if let Some(status) = self.status_mailbox.as_deref_mut() {
            status.is_comm_buffer_valid = 1; // TRUE
            log::trace!(target: "mm_comm", "Buffer {} status mailbox: IsCommBufferValid=TRUE", self.id);
            Ok(())
        } else {
            log::error!(target: "mm_comm", "Buffer {} has no status mailbox configured", self.id);
            Err(CommunicateBufferStatus::NoBuffer)
        }
    }

    /// Reads the return status from the MM communication after MMI completes.
    ///
    /// Returns the return status and buffer size set by the MM handler.
    ///
    /// ## Returns
    ///
    /// - `Ok((return_status, return_buffer_size))` if the status was read successfully
    /// - `Err(CommunicateBufferStatus)` if this buffer has no status mailbox configured
    pub fn get_mm_return_status(&self) -> Result<(u64, u64), CommunicateBufferStatus> {
        if let Some(status) = self.status_mailbox.as_deref() {
            // Copy packed fields to avoid unaligned reference errors
            let is_valid = status.is_comm_buffer_valid;
            let return_status = status.return_status;
            let return_buffer_size = status.return_buffer_size;

            log::trace!(
                target: "mm_comm",
                "Buffer {} return status: IsCommBufferValid={}, ReturnStatus=0x{:X}, ReturnBufferSize=0x{:X}",
                self.id,
                is_valid,
                return_status,
                return_buffer_size
            );
            Ok((return_status, return_buffer_size))
        } else {
            log::error!(target: "mm_comm", "Buffer {} has no status mailbox configured", self.id);
            Err(CommunicateBufferStatus::NoBuffer)
        }
    }

    /// Returns whether this buffer has a status mailbox configured.
    pub fn has_status_mailbox(&self) -> bool {
        self.status_mailbox.is_some()
    }

    /// Sets the result produced by an MM executor while exclusive access is held.
    pub fn set_mm_return_status(&mut self, status: u64, size: u64) -> Result<(), CommunicateBufferStatus> {
        let mailbox = self.status_mailbox.as_deref_mut().ok_or(CommunicateBufferStatus::NoBuffer)?;
        mailbox.return_status = status;
        mailbox.return_buffer_size = size;
        Ok(())
    }

    /// Resets the communication buffer by clearing all data and resetting internal state.
    pub fn reset(&mut self) {
        // Zero out the entire buffer
        self.as_slice_mut().fill(0);

        // Reset internal state
        self.private_message_length = 0;
        self.private_recipient = None;
    }

    /// Returns the available capacity for the message part of the communicate buffer.
    ///
    /// Note: Zero will be returned if the buffer is too small to hold the header.
    pub fn message_capacity(&self) -> usize {
        self.len().saturating_sub(Self::MESSAGE_START_OFFSET)
    }

    /// Verifies that the internal state matches what is in the memory buffer.
    /// This is intended to catch corruption and ensure the buffer actually matches what has
    /// been requested through the MM Communication API.
    ///
    /// Returns `Ok(())` if state verification passes, otherwise returns the appropriate error.
    fn verify_state_consistency(&self) -> Result<(), CommunicateBufferStatus> {
        let header_slice = self.as_slice().get(..Self::MESSAGE_START_OFFSET).ok_or_else(|| {
            log::error!(target: "mm_comm", "Buffer {} is too small for the communicate header", self.id);
            CommunicateBufferStatus::TooSmallForHeader
        })?;

        // SAFETY: Buffer size validated, BinaryGuid is repr(transparent) over repr(C) efi::Guid at offset 0.
        // read_unaligned is used because the buffer may not be aligned to the type's requirements.
        let memory_guid = unsafe { core::ptr::read_unaligned(header_slice.as_ptr().cast::<patina::BinaryGuid>()) };

        // SAFETY: Buffer size validated, usize at offset 16 after Guid.
        // read_unaligned is used because the buffer may not be aligned to usize requirements.
        let memory_message_length = unsafe { core::ptr::read_unaligned(header_slice.as_ptr().add(16).cast::<usize>()) };

        // Verify that thee recipient matches
        match self.private_recipient {
            Some(expected_guid) => {
                if memory_guid != expected_guid {
                    log::error!(target: "mm_comm", "Buffer {} GUID mismatch: private={:?}, memory={:?}",
                        self.id, expected_guid, memory_guid);
                    return Err(CommunicateBufferStatus::InvalidRecipient);
                }
            }
            None => {
                // If no recipient is set privately, the memory should contain all zeros for the GUID
                if memory_guid != patina::BinaryGuid::ZERO {
                    log::error!(target: "mm_comm", "Buffer {} unexpected GUID in memory when none set privately", self.id);
                    return Err(CommunicateBufferStatus::InvalidRecipient);
                }
            }
        }

        // Verify message length matches
        if memory_message_length != self.private_message_length {
            log::error!(target: "mm_comm", "Buffer {} message length mismatch: private={}, memory={}",
                self.id, self.private_message_length, memory_message_length);
            return Err(CommunicateBufferStatus::TooSmallForMessage);
        }

        log::trace!(target: "mm_comm", "Buffer {} state consistency was verified successfully", self.id);
        Ok(())
    }

    /// Validates that the buffer can accommodate a header and message of the given size.
    ///
    /// ## Arguments
    /// - `message_size` - The size of the message to validate
    ///
    /// ## Returns
    /// - `Ok(())` - The buffer can safely hold the header and message
    /// - `Err(status)` - Buffer validation failed
    fn validate_capacity(&self, message_size: usize) -> Result<(), CommunicateBufferStatus> {
        log::trace!(target: "mm_comm", "Validating capacity for buffer {}: buffer_size={}, message_size={}",
            self.id, self.len(), message_size);

        // First check if buffer can hold the header
        if self.len() < Self::MESSAGE_START_OFFSET {
            log::error!(target: "mm_comm", "Buffer {} too small for header: size={}, header_size={}",
                self.id, self.len(), Self::MESSAGE_START_OFFSET);
            return Err(CommunicateBufferStatus::TooSmallForHeader);
        }

        // Then check if remaining space can hold the message
        let available_message_space = self.len() - Self::MESSAGE_START_OFFSET;
        if message_size > available_message_space {
            log::error!(target: "mm_comm", "Buffer {} too small for message: available_space={}, message_size={}",
                self.id, available_message_space, message_size);
            return Err(CommunicateBufferStatus::TooSmallForMessage);
        }

        log::trace!(target: "mm_comm", "Buffer {} capacity validation passed", self.id);
        Ok(())
    }

    /// Sets the information needed for a communication message to be sent to the MM handler.
    /// Updates both the internal state and the memory buffer, then verifies consistency.
    ///
    /// ## Parameters
    ///
    /// - `recipient`: The GUID of the recipient MM handler.
    pub fn set_message_info(&mut self, recipient: Guid) -> Result<(), CommunicateBufferStatus> {
        log::trace!(target: "mm_comm", "Setting message info for buffer {}: recipient={}", self.id, recipient);

        // Validate capacity first
        self.validate_capacity(0)?;

        // Update private state
        let recipient_efi: BinaryGuid = recipient.to_efi_guid().into();
        self.private_recipient = Some(recipient_efi);

        // Update memory buffer using safe byte operations
        let header = EfiMmCommunicateHeader::new(recipient, self.private_message_length);
        let header_bytes = header.as_bytes();
        self.as_slice_mut()
            .get_mut(..Self::MESSAGE_START_OFFSET)
            .ok_or(CommunicateBufferStatus::TooSmallForHeader)?
            .copy_from_slice(header_bytes);

        // Verify state consistency after update
        self.verify_state_consistency()?;

        log::trace!(target: "mm_comm", "Message info set successfully for buffer {}", self.id);
        Ok(())
    }

    /// Sets the data message used for communication with the MM handler.
    /// Updates both the internal state and the memory buffer, then verifies consistency.
    ///
    /// ## Parameters
    ///
    /// - `message`: The message to be sent to the MM handler. The message length in the communicate header is
    ///   set to the length of this slice.
    pub fn set_message(&mut self, message: &[u8]) -> Result<(), CommunicateBufferStatus> {
        log::trace!(target: "mm_comm", "Setting message for buffer {}: message_size={}", self.id, message.len());

        self.validate_capacity(message.len())?;

        let recipient = self.private_recipient.ok_or_else(|| {
            log::error!(target: "mm_comm", "Buffer {} has no recipient set", self.id);
            CommunicateBufferStatus::InvalidRecipient
        })?;

        // Update private state
        self.private_message_length = message.len();

        log::trace!(target: "mm_comm", "Buffer {}: writing header and message data", self.id);

        // Update memory buffer using safe byte operations for header
        let header = EfiMmCommunicateHeader::new(Guid::from_ref(&recipient), message.len());
        let header_bytes = header.as_bytes();
        self.as_slice_mut()
            .get_mut(..Self::MESSAGE_START_OFFSET)
            .ok_or(CommunicateBufferStatus::TooSmallForHeader)?
            .copy_from_slice(header_bytes);

        // Copy message data
        self.as_slice_mut()
            .get_mut(Self::MESSAGE_START_OFFSET..Self::MESSAGE_START_OFFSET + message.len())
            .ok_or(CommunicateBufferStatus::TooSmallForMessage)?
            .copy_from_slice(message);

        // Verify state consistency after update
        self.verify_state_consistency()?;

        log::debug!(target: "mm_comm", "Buffer {} message set successfully: header_size={}, message_size={}",
            self.id, Self::MESSAGE_START_OFFSET, message.len());
        Ok(())
    }

    /// Returns a copy of the message part of the communicate buffer.
    /// This method uses the internal state and verifies consistency with memory.
    ///
    /// Note: This method extracts the actual message content using verified state tracking.
    pub fn get_message(&self) -> Result<Vec<u8>, CommunicateBufferStatus> {
        // Verify state consistency before proceeding
        self.verify_state_consistency()?;

        if self.private_message_length == 0 {
            log::trace!(target: "mm_comm", "Buffer {} has zero-length message", self.id);
            return Ok(Vec::new());
        }

        let start_offset = Self::MESSAGE_START_OFFSET;
        let end_offset = start_offset + self.private_message_length;

        let message = self
            .as_slice()
            .get(start_offset..end_offset)
            .ok_or_else(|| {
                log::error!(
                    target: "mm_comm",
                    "Buffer {} message extends beyond buffer: end_offset={}, buffer_len={}",
                    self.id,
                    end_offset,
                    self.len()
                );
                CommunicateBufferStatus::TooSmallForMessage
            })?
            .to_vec();
        log::trace!(target: "mm_comm", "Retrieved message from buffer {}: message_size={}", self.id, message.len());
        Ok(message)
    }

    /// Returns the header GUID from the current communicate buffer.
    /// This method uses the internal state and verifies consistency with memory.
    ///
    /// Returns `None` if no recipient has been set.
    pub fn get_header_guid(&self) -> Result<Option<Guid<'_>>, CommunicateBufferStatus> {
        // Verify state consistency first
        self.verify_state_consistency()?;

        log::trace!(target: "mm_comm", "Buffer {} header GUID retrieved from private state", self.id);
        Ok(self.private_recipient.as_ref().map(Guid::from))
    }

    /// Returns the message length from the current communicate buffer.
    /// This method uses the internal state and verifies consistency with memory.
    pub fn get_message_length(&self) -> Result<usize, CommunicateBufferStatus> {
        // Verify state consistency first
        self.verify_state_consistency()?;

        log::trace!(target: "mm_comm", "Buffer {} message length retrieved from private state: len={}",
            self.id, self.private_message_length);
        Ok(self.private_message_length)
    }
}

#[cfg_attr(coverage, coverage(off))]
impl fmt::Debug for CommunicateBufferAccess {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writelncrlf!(f, "CommunicateBuffer(id: 0x{:X}. len: 0x{:X})", self.id(), self.len())?;
        for (i, chunk) in self.as_slice().chunks(16).enumerate() {
            // Print the offset
            write!(f, "{:08X}: ", i * 16)?;
            // Print the hex values
            for byte in chunk {
                write!(f, "{byte:02X} ")?;
            }
            // Add spacing for incomplete rows
            if chunk.len() < 16 {
                write!(f, "{}", "   ".repeat(16 - chunk.len()))?;
            }
            // Print ASCII representation
            write!(f, " |")?;
            for byte in chunk {
                if byte.is_ascii_graphic() || *byte == b' ' {
                    write!(f, "{}", *byte as char)?;
                } else {
                    write!(f, ".")?;
                }
            }
            writelncrlf!(f, "|")?;
        }
        Ok(())
    }
}

/// Management Mode Interrupt (MMI) Port
#[derive(Copy, Clone)]
pub enum MmiPort {
    /// System Management Interrupt (SMI) Port for MM communication
    ///
    /// An SMI Port is a 16-bit integer value which indicates the port used for SMI communication.
    Smi(u16),
    /// Secure Monitor Call (SMC) Function ID for MM communication
    ///
    /// An SMC Function Identifier is a 32-bit integer value which indicates which function is being requested by
    /// the caller. It is always passed as the first argument to every SMC call in R0 or W0.
    Smc(u32),
}

impl fmt::Debug for MmiPort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MmiPort::Smi(port) => write!(f, "MmiPort::Smi(0x{port:04X})"),
            MmiPort::Smc(port) => write!(f, "MmiPort::Smc(0x{port:08X})"),
        }
    }
}

impl fmt::Display for MmiPort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MmiPort::Smi(value) => write!(f, "SMI(0x{value:04X})"),
            MmiPort::Smc(value) => write!(f, "SMC(0x{value:08X})"),
        }
    }
}

/// ACPI Base Address
///
/// Represents the base address for ACPI MMIO or IO ports. This is the address used to access the ACPI Fixed hardware
/// register set.
#[derive(PartialEq, Copy, Clone)]
pub enum AcpiBase {
    /// Memory-mapped IO (MMIO) base address for ACPI
    Mmio(usize),
    /// IO port base address for ACPI
    Io(u16),
}

impl fmt::Debug for AcpiBase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AcpiBase::Mmio(addr) => write!(f, "AcpiBase::Mmio(0x{addr:X})"),
            AcpiBase::Io(port) => write!(f, "AcpiBase::Io(0x{port:04X})"),
        }
    }
}

impl fmt::Display for AcpiBase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AcpiBase::Mmio(addr) => write!(f, "MMIO(0x{addr:X})"),
            AcpiBase::Io(port) => write!(f, "IO(0x{port:04X})"),
        }
    }
}

impl From<*const u32> for AcpiBase {
    fn from(ptr: *const u32) -> Self {
        let addr = ptr as usize;
        AcpiBase::Mmio(addr)
    }
}

impl From<*const u64> for AcpiBase {
    fn from(ptr: *const u64) -> Self {
        let addr = ptr as usize;
        AcpiBase::Mmio(addr)
    }
}

impl From<usize> for AcpiBase {
    fn from(addr: usize) -> Self {
        AcpiBase::Mmio(addr)
    }
}

impl From<u16> for AcpiBase {
    fn from(port: u16) -> Self {
        AcpiBase::Io(port)
    }
}

impl AcpiBase {
    /// Returns the IO port if this is an IO base, otherwise returns 0.
    pub fn get_io_value(&self) -> u16 {
        match self {
            AcpiBase::Mmio(_) => 0,
            AcpiBase::Io(port) => *port,
        }
    }

    /// Returns the MMIO address if this is an MMIO base, otherwise returns 0.
    pub fn get_mmio_value(&self) -> usize {
        match self {
            AcpiBase::Mmio(addr) => *addr,
            AcpiBase::Io(_) => 0,
        }
    }
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
mod tests {
    use super::CommunicateBufferAccess as CommunicateBuffer;
    use super::*;

    #[repr(align(4096))]
    struct AlignedBuffer([u8; 64]);

    #[test]
    fn test_communicate_buffer_aliases_serialize_and_share_metadata() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<super::CommunicateBuffer>();
        assert_send_sync::<MmCommunicationConfiguration>();

        let buffer = super::CommunicateBuffer::new(Pin::new(Box::leak(Box::new([0u8; 128]))), 1, mock_tpl_service());
        let alias = buffer.clone();
        let mut access = buffer.try_lock().unwrap();
        let guid = Guid::try_from_string("12345678-1234-5678-90AB-CDEF01234567").unwrap();
        access.set_message_info(guid).unwrap();
        access.set_message(b"shared").unwrap();

        std::thread::spawn(move || {
            assert!(matches!(alias.try_lock(), Err(CommunicateBufferStatus::Busy)));
        })
        .join()
        .unwrap();
        drop(access);
        assert_eq!(buffer.clone().try_lock().unwrap().get_message().unwrap(), b"shared");
        buffer.try_lock().unwrap().disable();
        assert!(!buffer.clone().try_lock().unwrap().is_enabled());
    }

    #[test]
    fn test_communicate_buffer_mailbox_aliases_and_firmware_updates_share_lock() {
        #[repr(align(4096))]
        struct Page([u8; 4096]);
        let page = Box::leak(Box::new(Page([0; 4096])));
        let mailbox = Box::leak(Box::new(MmCommBufferStatus::new()));
        let address = page.0.as_mut_ptr() as u64;
        let status_address = core::ptr::from_mut(mailbox) as u64;
        // SAFETY: Both allocations are exclusive static normal RAM and do not overlap.
        let buffer = unsafe {
            super::CommunicateBuffer::from_firmware_region(address, 4096, 1, Some(status_address), mock_tpl_service())
        }
        .unwrap();
        let alias = buffer.clone();
        let mut access = buffer.try_lock().unwrap();
        // SAFETY: Repeating the current description preserves the existing references.
        unsafe { access.replace_firmware_region(address, 4096, status_address) }.unwrap();
        access.set_comm_buffer_valid().unwrap();
        access.set_mm_return_status(7, 42).unwrap();
        assert!(matches!(alias.try_lock(), Err(CommunicateBufferStatus::Busy)));
        drop(access);
        assert_eq!(alias.try_lock().unwrap().get_mm_return_status().unwrap(), (7, 42));
        // SAFETY: Only a rejected overlapping description is supplied; no memory is accessed.
        let overlap = unsafe { buffer.try_lock().unwrap().replace_firmware_region(address, 4096, status_address + 1) };
        assert!(matches!(overlap, Err(CommunicateBufferStatus::AddressValidationFailed)));
    }

    #[test]
    fn test_set_message_info_success() {
        let buffer: &'static mut [u8; 64] = Box::leak(Box::new([0u8; 64]));
        let mut comm_buffer = CommunicateBuffer::new(Pin::new(buffer), 1);

        let recipient_guid = Guid::try_from_string("12345678-1234-5678-90AB-CDEF01234567").unwrap();
        let expected_bytes = recipient_guid.as_bytes();

        assert!(comm_buffer.set_message_info(recipient_guid).is_ok());

        // Test that state verification works
        assert!(comm_buffer.get_header_guid().is_ok());
        assert_eq!(comm_buffer.get_header_guid().unwrap().as_ref().map(patina::Guid::as_bytes), Some(expected_bytes));
    }

    #[test]
    fn test_set_message_info_failure_too_small_for_header() {
        let buffer: &'static mut [u8; 2] = Box::leak(Box::new([0u8; 2]));
        let mut comm_buffer = CommunicateBuffer::new(Pin::new(buffer), 1);

        let recipient_guid = Guid::try_from_string("12345678-1234-5678-90AB-CDEF01234567").unwrap();

        // The buffer is too small to hold the header, so this should fail
        assert_eq!(comm_buffer.set_message_info(recipient_guid), Err(CommunicateBufferStatus::TooSmallForHeader));
    }

    #[test]
    fn test_set_message_failure_too_small_for_message() {
        let buffer: &'static mut [u8; CommunicateBuffer::MINIMUM_BUFFER_SIZE] =
            Box::leak(Box::new([0u8; CommunicateBuffer::MINIMUM_BUFFER_SIZE]));
        let mut comm_buffer = CommunicateBuffer::new(Pin::new(buffer), 1);

        let recipient_guid = Guid::try_from_string("12345678-1234-5678-90AB-CDEF01234567").unwrap();

        assert_eq!(comm_buffer.set_message_info(recipient_guid), Ok(()));

        assert_eq!(
            comm_buffer.set_message("Test message data".as_bytes()),
            Err(CommunicateBufferStatus::TooSmallForMessage)
        );
    }

    #[test]
    fn test_set_message_failure_invalid_recipient() {
        let buffer: &'static mut [u8; 64] = Box::leak(Box::new([0u8; 64]));
        let mut comm_buffer = CommunicateBuffer::new(Pin::new(buffer), 1);

        // Should fail because no recipient was set
        assert_eq!(
            comm_buffer.set_message("Test message data".as_bytes()),
            Err(CommunicateBufferStatus::InvalidRecipient)
        );
    }

    #[test]
    fn test_set_message_success() {
        let buffer: &'static mut [u8; 64] = Box::leak(Box::new([0u8; 64]));
        let mut comm_buffer = CommunicateBuffer::new(Pin::new(buffer), 1);

        let recipient_guid = Guid::try_from_string("12345678-1234-5678-90AB-CDEF01234567").unwrap();
        assert!(comm_buffer.set_message_info(recipient_guid).is_ok());

        let message = b"MM Handler!";
        assert!(comm_buffer.set_message(message).is_ok());
        assert_eq!(comm_buffer.len(), 64);
        assert!(!comm_buffer.is_empty());
        assert_eq!(comm_buffer.id(), 1);

        // Test that we can retrieve the message
        let retrieved_message = comm_buffer.get_message().unwrap();
        assert_eq!(retrieved_message, message);

        // Test that state verification is successful
        assert_eq!(comm_buffer.get_message_length().unwrap(), message.len());
    }

    #[test]
    fn test_set_message_failure_buffer_too_small() {
        // The buffer is too small for the header - capacity validation happens first
        let buffer: &'static mut [u8; 16] = Box::leak(Box::new([0u8; 16]));
        let mut comm_buffer = CommunicateBuffer::new(Pin::new(buffer), 1);

        let message = b"MM Handler!";
        assert_eq!(comm_buffer.set_message(message), Err(CommunicateBufferStatus::TooSmallForHeader));

        // The buffer has room for the header but there is not enough room for the message
        let buffer2: &'static mut [u8; 30] = Box::leak(Box::new([0u8; 30]));
        let mut comm_buffer2 = CommunicateBuffer::new(Pin::new(buffer2), 2);

        let recipient_guid = Guid::try_from_string("12345678-1234-5678-90AB-CDEF01234567").unwrap();
        assert!(comm_buffer2.set_message_info(recipient_guid).is_ok());

        let long_message = b"This message is too long for the remaining space!";
        assert_eq!(comm_buffer2.set_message(long_message), Err(CommunicateBufferStatus::TooSmallForMessage));
    }

    #[test]
    fn test_get_message_success() {
        const MESSAGE: &[u8] = b"MM Handler!";
        const COMM_BUFFER_SIZE: usize = CommunicateBuffer::MESSAGE_START_OFFSET + MESSAGE.len();

        let buffer: &'static mut [u8; COMM_BUFFER_SIZE] = Box::leak(Box::new([0u8; COMM_BUFFER_SIZE]));
        let mut comm_buffer = CommunicateBuffer::new(Pin::new(buffer), 1);

        let test_guid = Guid::try_from_string("12345678-1234-5678-90AB-CDEF01234567").unwrap();

        assert!(comm_buffer.set_message_info(test_guid).is_ok(), "Failed to set the message info");
        assert!(comm_buffer.set_message(MESSAGE).is_ok(), "Failed to set the message");

        let retrieved_message = comm_buffer.get_message().unwrap();
        assert_eq!(retrieved_message, MESSAGE.to_vec());
    }

    #[test]
    fn test_set_message_info_multiple_times_success() {
        let buffer: &'static mut [u8; 64] = Box::leak(Box::new([0u8; 64]));
        let mut comm_buffer = CommunicateBuffer::new(Pin::new(buffer), 1);

        let recipient_guid = Guid::try_from_string("12345678-1234-5678-90AB-CDEF01234567").unwrap();
        assert!(comm_buffer.set_message_info(recipient_guid.clone()).is_ok());
        assert_eq!(
            comm_buffer.get_header_guid().unwrap().as_ref().map(patina::Guid::as_bytes),
            Some(recipient_guid.as_bytes())
        );

        let message = b"MM Handler!";
        assert!(comm_buffer.set_message(message).is_ok());
        assert_eq!(comm_buffer.get_message().unwrap(), message.to_vec());
        assert_eq!(comm_buffer.len(), 64);
        assert_eq!(comm_buffer.get_message_length().unwrap(), message.len());

        // Update with new recipient
        let recipient_guid2 = Guid::try_from_string("3210FEDC-ABCD-ABCD-1223-1234567890AB").unwrap();
        assert!(comm_buffer.set_message_info(recipient_guid2.clone()).is_ok());
        assert_eq!(
            comm_buffer.get_header_guid().unwrap().as_ref().map(patina::Guid::as_bytes),
            Some(recipient_guid2.as_bytes())
        );

        // Message should still be there but header should be updated
        assert_eq!(comm_buffer.get_message().unwrap(), message.to_vec());
        assert_eq!(comm_buffer.len(), 64);
        assert_eq!(comm_buffer.get_message_length().unwrap(), message.len());
    }

    #[test]
    fn test_from_raw_parts_zero_size() {
        let buffer: &'static mut [u8; 0] = Box::leak(Box::new([]));
        let size = buffer.len();
        let id = 1;
        // SAFETY: Test validates error handling for zero-sized buffer
        let result = unsafe { CommunicateBuffer::from_raw_parts(buffer.as_mut_ptr(), size, id) };
        assert!(matches!(result, Err(CommunicateBufferStatus::TooSmallForHeader)));
    }

    #[test]
    fn test_from_raw_parts_null_pointer() {
        let buffer: *mut u8 = core::ptr::null_mut();
        let size = 64;
        let id = 1;
        // SAFETY: Test validates error handling for null pointer
        let result = unsafe { CommunicateBuffer::from_raw_parts(buffer, size, id) };
        assert!(matches!(result, Err(CommunicateBufferStatus::NoBuffer)));
    }

    #[test]
    fn test_set_comm_buffer_valid_without_status_mailbox() {
        let buffer: &'static mut [u8; 64] = Box::leak(Box::new([0u8; 64]));
        let mut comm_buffer = CommunicateBuffer::new(Pin::new(&mut buffer[..]), 1);
        assert!(matches!(comm_buffer.set_comm_buffer_valid(), Err(CommunicateBufferStatus::NoBuffer)));
    }

    #[test]
    fn test_get_mm_return_status_without_status_mailbox() {
        let buffer: &'static mut [u8; 64] = Box::leak(Box::new([0u8; 64]));
        let comm_buffer = CommunicateBuffer::new(Pin::new(&mut buffer[..]), 1);
        assert!(matches!(comm_buffer.get_mm_return_status(), Err(CommunicateBufferStatus::NoBuffer)));
    }

    #[test]
    fn test_from_firmware_region_success() {
        use patina::UEFI_PAGE_SIZE;

        let aligned_buf = Box::new(AlignedBuffer([0u8; 64]));
        let buffer_ptr = aligned_buf.0.as_ptr();
        assert_eq!(buffer_ptr as usize & (UEFI_PAGE_SIZE - 1), 0, "Buffer is not 4K aligned");

        let addr = buffer_ptr as u64;
        let size = 64;
        let id = 1;

        // SAFETY: Test buffer is 4K-aligned, valid, and leaked for static lifetime
        let result = unsafe { CommunicateBuffer::from_firmware_region(addr, size, id, None) };
        assert!(result.is_ok());
        let comm_buffer = result.unwrap();
        assert_eq!(comm_buffer.len(), size);
        assert_eq!(comm_buffer.id(), id);
    }

    #[test]
    fn test_from_firmware_region_overflow() {
        let addr = u64::MAX;
        let size = 1;
        let id = 1;

        // SAFETY: Test validates error handling for address overflow
        let result = unsafe { CommunicateBuffer::from_firmware_region(addr, size, id, None) };
        assert!(matches!(result, Err(CommunicateBufferStatus::AddressValidationFailed)));
    }

    #[test]
    fn test_from_raw_parts_success() {
        use patina::UEFI_PAGE_SIZE;

        let mut aligned_buf = Box::new(AlignedBuffer([0u8; 64]));
        let buffer = &mut aligned_buf.0;
        assert_eq!(buffer.as_ptr() as usize & (UEFI_PAGE_SIZE - 1), 0, "Buffer is not 4K aligned");

        let size = buffer.len();
        let id = 1;
        // SAFETY: Test buffer is 4K-aligned, valid, and owned by test
        let comm_buffer = unsafe { CommunicateBuffer::from_raw_parts(buffer.as_mut_ptr(), size, id).unwrap() };

        assert_eq!(comm_buffer.len(), size);
        assert_eq!(comm_buffer.id(), id);

        // Test that the buffer is zeroed initially
        assert_eq!(comm_buffer.get_header_guid().unwrap(), None);
        assert_eq!(comm_buffer.get_message_length().unwrap(), 0);
    }

    #[test]
    fn test_state_consistency_verification() {
        let buffer: &'static mut [u8; 64] = Box::leak(Box::new([0u8; 64]));
        let mut comm_buffer = CommunicateBuffer::new(Pin::new(buffer), 1);

        let test_guid = Guid::try_from_string("12345678-1234-5678-90AB-CDEF01234567").unwrap();
        let test_message = b"test message";

        assert!(comm_buffer.set_message_info(test_guid.clone()).is_ok());
        assert!(comm_buffer.set_message(test_message).is_ok());

        // Test that the getters pass consistency checks and return the expected values
        assert_eq!(
            comm_buffer.get_header_guid().unwrap().as_ref().map(patina::Guid::as_bytes),
            Some(test_guid.as_bytes())
        );
        assert_eq!(comm_buffer.get_message_length().unwrap(), test_message.len());
        assert_eq!(comm_buffer.get_message().unwrap(), test_message.to_vec());
    }

    #[test]
    fn test_buffer_too_small_for_header_operations() {
        let buffer: &'static mut [u8; 2] = Box::leak(Box::new([0u8; 2]));
        let comm_buffer = CommunicateBuffer::new(Pin::new(buffer), 1);

        // All operations should fail with appropriate errors for undersized buffers
        assert!(matches!(comm_buffer.get_header_guid(), Err(CommunicateBufferStatus::TooSmallForHeader)));
        assert!(matches!(comm_buffer.get_message_length(), Err(CommunicateBufferStatus::TooSmallForHeader)));
        assert!(matches!(comm_buffer.get_message(), Err(CommunicateBufferStatus::TooSmallForHeader)));
    }

    // Tests for other structures remain the same as they don't depend on CommunicateBuffer
    #[test]
    fn test_smiport_debug_msg() {
        let smi_port = MmiPort::Smi(0xFF);
        let debug_msg: String = format!("{smi_port:?}");
        assert_eq!(debug_msg, "MmiPort::Smi(0x00FF)");
    }

    #[test]
    fn test_smcport_debug_msg_smc() {
        let smc_port = MmiPort::Smc(0x12345678);
        let debug_msg = format!("{smc_port:?}");
        assert_eq!(debug_msg, "MmiPort::Smc(0x12345678)");
    }

    #[test]
    fn test_acpibase_debug_msg() {
        let acpi_base_mmio = AcpiBase::Mmio(0x12345678);
        let debug_msg_mmio = format!("{acpi_base_mmio:?}");
        assert_eq!(debug_msg_mmio, "AcpiBase::Mmio(0x12345678)");

        let acpi_base_io = AcpiBase::Io(0x1234);
        let debug_msg_io = format!("{acpi_base_io:?}");
        assert_eq!(debug_msg_io, "AcpiBase::Io(0x1234)");
    }

    #[test]
    fn test_acpibase_display_msg() {
        let acpi_base_mmio = AcpiBase::Mmio(0x12345678);
        let display_msg_mmio = format!("{acpi_base_mmio}");
        assert_eq!(display_msg_mmio, "MMIO(0x12345678)");

        let acpi_base_io = AcpiBase::Io(0x1234);
        let display_msg_io = format!("{acpi_base_io}");
        assert_eq!(display_msg_io, "IO(0x1234)");
    }

    #[test]
    fn test_mmiport_display_msg() {
        let smi_port = MmiPort::Smi(0xFF);
        let display_msg_smi = format!("{smi_port}");
        assert_eq!(display_msg_smi, "SMI(0x00FF)");

        let smc_port = MmiPort::Smc(0x12345678);
        let display_msg_smc = format!("{smc_port}");
        assert_eq!(display_msg_smc, "SMC(0x12345678)");
    }

    #[test]
    fn test_acpibase_get_io_value() {
        let acpi_base = AcpiBase::Io(0x1234);
        assert_eq!(acpi_base.get_io_value(), 0x1234);
    }

    #[test]
    fn test_acpibase_get_mmio_value() {
        let acpi_base = AcpiBase::Mmio(0x12345678);
        assert_eq!(acpi_base.get_mmio_value(), 0x12345678);
    }

    #[test]
    fn test_acpibase_from_u32_ptr() {
        let ptr: *const u32 = 0x12345678 as *const u32;
        let acpi_base: AcpiBase = ptr.into();
        assert_eq!(acpi_base, AcpiBase::Mmio(0x12345678));
    }

    #[test]
    fn test_acpibase_from_u64_ptr() {
        let ptr: *const u64 = 0x0123456789ABCDEF as *const u64;
        let acpi_base: AcpiBase = ptr.into();
        assert_eq!(acpi_base, AcpiBase::Mmio(0x0123456789ABCDEF));
    }

    #[test]
    fn test_acpibase_from_usize() {
        let addr: usize = 0x12345678;
        let acpi_base: AcpiBase = addr.into();
        assert_eq!(acpi_base, AcpiBase::Mmio(0x12345678));
    }

    #[test]
    fn test_acpibase_from_u16() {
        let port: u16 = 0x1234;
        let acpi_base: AcpiBase = port.into();
        assert_eq!(acpi_base, AcpiBase::Io(0x1234));
    }

    #[test]
    fn test_efi_mm_communicate_header_header_guid() {
        let test_guid = Guid::try_from_string("12345678-1234-5678-90AB-CDEF01234567").unwrap();
        let message_length = 42usize;

        let header = EfiMmCommunicateHeader::new(test_guid.clone(), message_length);

        let returned_guid = header.header_guid();
        assert_eq!(returned_guid.as_bytes(), test_guid.as_bytes());

        let test_guid2 = Guid::try_from_string("DEADBEEF-CAFE-DCBA-1234-56789ABCDEF0").unwrap();
        let header2 = EfiMmCommunicateHeader::new(test_guid2.clone(), message_length);

        let returned_guid2 = header2.header_guid();
        assert_eq!(returned_guid2.as_bytes(), test_guid2.as_bytes());

        assert_ne!(returned_guid.as_bytes(), returned_guid2.as_bytes());
    }

    #[test]
    fn test_efi_mm_communicate_header_message_length() {
        let test_guid = Guid::try_from_string("12345678-1234-5678-90AB-CDEF01234567").unwrap();

        let test_lengths = [0usize, 1, 42, 1024, usize::MAX];

        for &length in &test_lengths {
            let header = EfiMmCommunicateHeader::new(test_guid.clone(), length);
            assert_eq!(header.message_length(), length);
        }
    }

    #[test]
    fn test_efi_mm_communicate_header_size() {
        let expected_size = core::mem::size_of::<patina::BinaryGuid>() + core::mem::size_of::<usize>();
        assert_eq!(EfiMmCommunicateHeader::size(), expected_size);

        let test_guid = Guid::try_from_string("12345678-1234-5678-90AB-CDEF01234567").unwrap();
        let header = EfiMmCommunicateHeader::new(test_guid, 42);
        assert_eq!(header.as_bytes().len(), EfiMmCommunicateHeader::size());
    }

    #[test]
    fn test_mm_communication_configuration_display() {
        let default_config = MmCommunicationConfiguration::default();
        let display_output = format!("{default_config}");

        let expected_lines = [
            "MM Communication Configuration:",
            "  ACPI Base: MMIO(0x0)",
            "  Command Port: SMI(0x00FF)",
            "  Data Port: SMI(0x0000)",
            "  Communication Buffers (0):",
            "    <none>",
        ];

        for expected_line in &expected_lines {
            assert!(
                display_output.contains(expected_line),
                "Display output should contain: '{expected_line}'\nActual output:\n{display_output}"
            );
        }

        let buffer1: &'static mut [u8; 64] = Box::leak(Box::new([0u8; 64]));
        let buffer2: &'static mut [u8; 128] = Box::leak(Box::new([0u8; 128]));

        let comm_buffer1 = super::CommunicateBuffer::new(Pin::new(buffer1), 1, mock_tpl_service());
        let comm_buffer2 = super::CommunicateBuffer::new(Pin::new(buffer2), 2, mock_tpl_service());

        let populated_config = MmCommunicationConfiguration {
            acpi_base: AcpiBase::Io(0x1234),
            cmd_port: MmiPort::Smc(0x87654321),
            data_port: MmiPort::Smi(0xABCD),
            comm_buffers: vec![comm_buffer1, comm_buffer2],
            enable_comm_buffer_updates: false,
            updatable_buffer_id: None,
        };

        let populated_display = format!("{populated_config}");

        assert!(populated_display.contains("MM Communication Configuration:"));
        assert!(populated_display.contains("  ACPI Base: IO(0x1234)"));
        assert!(populated_display.contains("  Command Port: SMC(0x87654321)"));
        assert!(populated_display.contains("  Data Port: SMI(0xABCD)"));
        assert!(populated_display.contains("  Communication Buffers (2):"));

        assert!(populated_display.contains("Buffer 0x01:"));
        assert!(populated_display.contains("Buffer 0x02:"));
        assert!(populated_display.contains("len=0x40")); // 64 bytes = 0x40
        assert!(populated_display.contains("len=0x80")); // 128 bytes = 0x80
    }
}
