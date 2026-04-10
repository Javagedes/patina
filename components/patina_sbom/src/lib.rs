pub mod component;

use patina_acpi::service::AcpiTableHeader;

use zerocopy_derive::*;

#[repr(C, packed)]
#[derive(IntoBytes, FromBytes, KnownLayout, Immutable)]
struct EfiAcpiSbomTable {
    header: AcpiTableHeader,
    entries: [u8],
}

#[repr(C, packed)]
#[derive(IntoBytes, FromBytes, KnownLayout, Immutable)]
struct AcpiSbomTableEntry {
    length: u32,
    revision: u8,
    format: u8,
    reserved: [u8; 2],
    data: [u8],
}