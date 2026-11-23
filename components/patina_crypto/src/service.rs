//! Cryptographic service interfaces.
//!
//! Four services cover the cryptographic functionality of EDK II `BaseCryptLib`:
//!
//! - [`hash::Hash`]: digests, MACs, and key derivation.
//! - [`encryption::Encryption`]: symmetric and asymmetric encryption.
//! - [`signature::Signature`]: signing, verification, and certificate and signed data inspection.
//! - [`random::Random`]: random number generation.
//!
//! Services are algorithm agile: an algorithm enum and key are selected once, and the service returns a generic handle
//! (such as a `DigestContext`, `Cipher`, `Signer`, or `Verifier`) that works the same way for every algorithm.
//! Handles own their provider resources and release them when dropped. `*Ext` traits provide one-shot convenience
//! methods.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
pub use patina::crypto::{encryption, hash, random, signature};
