# Patina SBOM

`patina_sbom` collects Software Bill of Materials payloads during DXE and publishes them through
the SBOM ACPI table at Ready-to-Boot.

The staging table uses ordinary boot-services allocation while entries are registered. At
Ready-to-Boot, the ACPI service validates and copies the complete table into `ACPIReclaimMemory`,
adds it to the XSDT, and owns the published allocation.

## Integration

Register shared OEM information and the component:

```rust,ignore
use patina::oem::OemInfo;
use patina_acpi::component::AcpiComponent;
use patina_sbom::component::SbomComponent;

let oem = OemInfo::new(*b"OEM_ID", *b"TABLE_ID", 1, u32::from_le_bytes(*b"PTNA"), 1);
add.config(oem);
add.component(AcpiComponent::new());
add.component(SbomComponent::new());
```

Both components consume the shared OEM configuration. The SBOM component also waits until the
ACPI Table Protocol is installed before it dispatches.

Components can then register entries through `Service<dyn Sbom>`:

```rust,ignore
use patina::component::service::Service;
use patina::acpi::{
    EFI_ACPI_SBOM_TABLE_ENTRY_FLAG_NONE,
    EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_COMPRESSION_NONE,
    EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_FORMAT_SPDX,
};
use patina_sbom::service::Sbom;

fn register_sbom(sbom: Service<dyn Sbom>, payload: &[u8]) -> Result<(), patina_sbom::error::SbomError> {
    sbom.add_entry(
        EFI_ACPI_SBOM_TABLE_ENTRY_FLAG_NONE,
        EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_FORMAT_SPDX,
        EFI_ACPI_SBOM_TABLE_ENTRY_SBOM_COMPRESSION_NONE,
        payload,
    )
}
```
