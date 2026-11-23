//! Algorithm-agile cryptographic service interfaces.
//!
//! Providers implement these interfaces independently of their consumers.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
pub mod encryption;
pub mod error;
pub mod hash;
pub mod random;
pub mod signature;
