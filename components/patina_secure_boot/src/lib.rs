//! Secure Boot verification of original PE/COFF image bytes.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![cfg_attr(coverage, feature(coverage_attribute))]
#![deny(missing_docs)]
extern crate alloc;

pub mod component;
pub mod database;
mod image;
mod measurement;
#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
mod test_support;
mod verification;
