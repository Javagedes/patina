//! Software Bill of Materials (SBOM) ACPI table component.
//!
//! The crate collects SBOM entries in a boot-services staging buffer and publishes the completed
//! ACPI table at Ready-to-Boot.
//!
//! ## License
//!
//! Copyright (C) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
#![cfg_attr(all(not(feature = "std"), not(test), not(feature = "mockall")), no_std)]
#![deny(missing_docs)]
#![cfg_attr(coverage, feature(coverage_attribute))]

extern crate alloc;

pub mod component;
pub mod error;
pub mod service;
