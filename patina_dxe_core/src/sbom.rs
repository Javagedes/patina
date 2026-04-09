use zerocopy::{FromBytes, IntoBytes};
use zerocopy_derive::*;

use alloc::alloc::{Allocator, Global, Layout};

use patina::{base::UEFI_PAGE_SIZE, component::service::memory::{AllocationOptions, MemoryManager}};


#[repr(C, packed)]
#[derive(IntoBytes, FromBytes, KnownLayout, Immutable)]
struct EfiAcpiDescriptionHeader {
    signature: u32,
    length: u32,
    revision: u8,
    checksum: u8,
    oem_id: [u8; 6],
    oem_table_id: u64,
    oem_revision: u32,
    creator_id: u32,
    creator_revision: u32,
}

struct EfiAcpiSbomTable {
    header: EfiAcpiDescriptionHeader,
    entries: [u8],
}

#[repr(C, packed)]
#[derive(IntoBytes, FromBytes, KnownLayout, Immutable)]
struct EfiAcpiSbomTableEntry {
    length: u32,
    revision: u8,
    format: u8,
    reserved: [u8; 2],
    data: [u8],
}

pub struct AcpiSbomTable<A: Allocator = Global> {
    alloc: A,
    layout: Layout,
    bytes: &'static mut [u8],
}

impl AcpiSbomTable {
    pub fn new() -> Self {
        Self::new_in(Global)
    }
}

impl <A: Allocator> AcpiSbomTable<A> {
    pub fn new_in(alloc: A) -> Self {
        const HEADER: EfiAcpiDescriptionHeader = EfiAcpiDescriptionHeader {
            signature: u32::from_le_bytes(*b"SBOM"),
            length: core::mem::size_of::<EfiAcpiDescriptionHeader>() as u32,
            revision: 1,
            checksum: 0,
            oem_id: *b"Patina",
            oem_table_id: 0,
            oem_revision: 0,
            creator_id: 0,
            creator_revision: 0,
        };

        let layout = Layout::array::<u8>(UEFI_PAGE_SIZE).unwrap();

        let mut x = alloc.allocate_zeroed(layout).unwrap();
        
        Self {
            alloc,
            layout,
            // SAFETY: `Self` is the only owner of the allocated memory
            bytes: unsafe { x.as_mut() }
        }
    }

    pub fn length(&self) -> usize {
        let (header, _) = EfiAcpiDescriptionHeader::read_from_prefix(self.bytes).unwrap();
        header.length as usize
    }

    /// Adds an SBOM entry to the table, growing the underlying buffer if necessary.
    /// 
    /// ## Errors
    /// 
    /// Returns an [alloc::alloc::AllocError] if an allocation is necessary and the allocation fails.
    pub fn add_entry(&mut self, entry: &EfiAcpiSbomTableEntry) -> Result<(), alloc::alloc::AllocError> {
        let entry_bytes = entry.as_bytes();
        let entry_len = entry_bytes.len();
        let offset = self.length();
        let new_len = offset + entry_len;

        if new_len > self.bytes.len() {
            self.grow(new_len)?;
        }

        self.bytes[offset..offset + entry_len].copy_from_slice(entry_bytes);

        Ok(())
    }

    /// Grows the underlying buffer to at least `new_len` bytes.
    ///
    /// ## Errors
    ///
    /// Returns an [alloc::alloc::AllocError] if the allocation fails.
    /// Returns an [alloc::alloc::AllocError] if the required layout is too large to be represented.
    fn grow(&mut self, min_length: usize) -> Result<(), alloc::alloc::AllocError> {
        let old_layout = self.layout;

        let new_length = (self.layout.size() * 2).max(patina::uefi_pages_to_size!(patina::uefi_size_to_pages!(min_length)));
        let new_layout = Layout::array::<u8>(new_length).map_err(|_| alloc::alloc::AllocError)?;

        let old_bytes_ptr = core::ptr::NonNull::from(&self.bytes).cast::<u8>();

        // SAFETY: `ptr` is a valid pointer allocated with `self.alloc`
        // SAFETY: `old_layout` is the exact layout that was used to allocate `ptr`
        // SAFETY: `new_layout` is guaranteed to be larger than `old_layout`
        self.bytes = unsafe { self.alloc.grow_zeroed(old_bytes_ptr, old_layout, new_layout)?.as_mut() };
        self.layout = new_layout;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
}
