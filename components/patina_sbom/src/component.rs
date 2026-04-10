use patina::component::{service::Service, component};
use patina_acpi::service::AcpiTableManager;

struct Sbom;

#[component]
impl Sbom {
    fn entry_point(self, acpi: Service<AcpiTableManager>) -> patina::error::Result<()> {
        
        unsafe { acpi.install_acpi_table() };
        
        Ok(())
    }
}
