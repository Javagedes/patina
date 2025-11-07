use std::{collections::HashSet, str::FromStr};

fn strip_colon(item: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    proc_macro2::TokenStream::from_str(item.to_string().strip_suffix(";").unwrap()).unwrap()
}

pub fn sbom2(item: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let s = strip_colon(item);
    let metadata = cargo_metadata::MetadataCommand::new()
        .exec()
        .unwrap();

    let config = cargo_cyclonedx::config::SbomConfig {
        format: Some(cargo_cyclonedx::format::Format::Xml),
        included_dependencies: Some(cargo_cyclonedx::config::IncludedDependencies::AllDependencies),
        output_options: Some(cargo_cyclonedx::config::OutputOptions {
            filename: cargo_cyclonedx::config::FilenamePattern::CrateName,
            platform_suffix: cargo_cyclonedx::config::PlatformSuffix::Included,
        }),
        features: Some(cargo_cyclonedx::config::Features {
            all_features: true,
            no_default_features: false,
            features: vec![],
        }),
        target: Some(cargo_cyclonedx::config::Target::AllTargets),
        license_parser: Some(cargo_cyclonedx::config::LicenseParserOptions {
            mode: cargo_cyclonedx::config::ParseMode::Lax,
            accept_named: HashSet::new(),
        }),
        describe: Some(cargo_cyclonedx::config::Describe::Binaries),
        spec_version: Some(cyclonedx_bom::models::bom::SpecVersion::V1_4),
        only_normal_deps: Some(true)
    };

    let sboms = cargo_cyclonedx::generator::SbomGenerator::create_sboms(
        metadata,
        &config,
    ).unwrap();

    for sbom in &sboms {
        println!("{}", sbom.package_name);
        println!("{:#?}", sbom.target_kinds);
    }
    println!("Generated SBOM: {:?}", sboms.len());

    quote::quote! {
        #s = &[];
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn simple_test() {
        let input = quote::quote! {
            static SBOM_DATA: [u8];
        };

        let output = super::sbom2(input);   
        println!("Output: {}", output);
    }
}