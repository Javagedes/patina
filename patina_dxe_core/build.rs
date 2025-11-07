use std::collections::HashSet;

struct Sbom {
    pub package_name: String,
    pub bytes: Vec<u8>,
}

fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    println!("cargo::rerun-if-env-changed=TARGET");

    let target = std::env::var("TARGET").expect("TARGET is always set");
    let out_dir = std::env::var("OUT_DIR").expect("OUT_DIR is always set");
    println!("cargo:warning=out_dir={}", out_dir);

    let features = std::env::vars()
        .filter_map(|(name, _)| {
            if name == "CARGO_FEATURE_DEFAULT" {
                return None;
            }

            if name.starts_with("CARGO_FEATURE_") {
                return Some(name.trim_start_matches("CARGO_FEATURE_").to_lowercase());
            }
            None
        })
        .collect::<Vec<_>>();

    let dir = std::env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR is always set");
    println!("cargo:warning=manifest_dir={}", dir);

    let metadata = cargo_metadata::MetadataCommand::new()
        .features(cargo_metadata::CargoOpt::SomeFeatures(features.clone()))
        .exec()
        .unwrap();

    let sbom_config = cargo_cyclonedx::config::SbomConfig {
        format: Some(cargo_cyclonedx::format::Format::Xml),
        included_dependencies: Some(cargo_cyclonedx::config::IncludedDependencies::AllDependencies),
        output_options: Some(cargo_cyclonedx::config::OutputOptions {
            filename: cargo_cyclonedx::config::FilenamePattern::CrateName,
            platform_suffix: cargo_cyclonedx::config::PlatformSuffix::Included,
        }),
        features: Some(cargo_cyclonedx::config::Features {
            all_features: false,
            no_default_features: false,
            features,
        }),
        target: Some(cargo_cyclonedx::config::Target::SingleTarget(target)),
        license_parser: Some(cargo_cyclonedx::config::LicenseParserOptions {
            mode: cargo_cyclonedx::config::ParseMode::Lax,
            accept_named: HashSet::new(),
        }),
        describe: Some(cargo_cyclonedx::config::Describe::Binaries),
        spec_version: Some(cyclonedx_bom::models::bom::SpecVersion::V1_4),
        only_normal_deps: Some(true),
    };

    let sboms = cargo_cyclonedx::generator::SbomGenerator::create_sboms(
        metadata,
        &sbom_config,
    ).unwrap();

    let sboms = sboms.into_iter().filter_map(|sbom| {
        println!("cargo:warning=Processing SBOM for package: {}", sbom.package_name);
        const CORE_NAME: &[u8] = b"patina_dxe_core";
        const CORE_NAME_LEN: usize = CORE_NAME.len();

        let package_name = sbom.package_name;
        
        let mut bytes: Vec<u8> = Vec::new();
        sbom.bom.output_as_xml_v1_4(&mut bytes).unwrap();
        if bytes.windows(CORE_NAME_LEN).any(|w| w == CORE_NAME) {
            return Some(Sbom { package_name, bytes });
        }
        None
    }).collect::<Vec<_>>();

    println!("cargo:warning=Generating {} SBOM(s)", sboms.len());

    for sbom in sboms {
        let file_name = format!("{}/{}_sbom.xml.deflate", out_dir, sbom.package_name);
        let bytes = miniz_oxide::deflate::compress_to_vec(&sbom.bytes, 10);
        if std::fs::exists(&file_name).unwrap() {
            std::fs::remove_file(&file_name).unwrap();
        }

        std::fs::write(&file_name, &bytes).unwrap();
        println!("cargo:warning=Generated SBOM at: {}", file_name);
    }

    // for sbom in sboms {
    //     let path = format!("{}/{}.xml", out_dir, sbom.package_name);
    //     println!("cargo:warning=Generating SBOM at: {}", path);
    //     if std::fs::exists(&path).unwrap() {
    //         std::fs::remove_file(&path).unwrap();
    //     }
    //     let mut file = std::fs::File::create(&path).unwrap();
    //     sbom.bom.output_as_xml_v1_4(&mut file).unwrap();
    // }

    
}