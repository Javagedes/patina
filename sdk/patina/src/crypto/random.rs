//! Random number service.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use crate::crypto::error::Result;

#[cfg(any(test, feature = "mockall"))]
use mockall::automock;

/// Pseudo-random number generation.
///
/// Equivalent to the `Random*` functions in `BaseCryptLib`.
#[cfg_attr(any(test, feature = "mockall"), automock)]
pub trait Random {
    /// Seeds the generator with `seed`, or with provider entropy when `seed` is `None`.
    #[allow(clippy::needless_lifetimes, reason = "mockall requires explicit lifetimes for nested references")]
    fn seed<'a>(&self, seed: Option<&'a [u8]>) -> Result<()>;

    /// Fills `output` with pseudo-random bytes.
    fn fill_bytes(&self, output: &mut [u8]) -> Result<()>;
}
