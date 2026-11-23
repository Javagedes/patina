//! Cryptographic services for Patina.
//!
//! This crate defines Rust service interfaces equivalent to EDK II `BaseCryptLib`. Each capability is algorithm
//! agile: the algorithm and key are selected once through a single constructor, which returns a generic handle that
//! works the same way for every algorithm. `*Ext` traits provide one-shot helpers on top of the handles.
//!
//! | Service | Handle | `BaseCryptLib` functionality |
//! |---------|--------|------------------------------|
//! | [`Hash`](service::hash::Hash) | [`DigestContext`](service::hash::DigestContext) | SHA-1/SHA-2 hashing, HMAC, PBKDF2, and HKDF |
//! | [`Encryption`](service::encryption::Encryption) | [`Cipher`](service::encryption::Cipher) | AES-CBC, AES-GCM, RSA-OAEP, PKCS#7 enveloped data |
//! | [`Signature`](service::signature::Signature) | [`Signer`](service::signature::Signer) / [`Verifier`](service::signature::Verifier) | RSA PKCS#1 v1.5 and PSS, ECDSA, PKCS#7, CMS, and Authenticode signatures, plus X.509, PKCS#7, and Authenticode certificate inspection |
//! | [`Random`](service::random::Random) | | Pseudo-random number generation |
//!
//! ## Implementations
//!
//! [`OneCryptoComponent`](component::OneCryptoComponent) produces every service from the `OneCrypto` protocol once
//! it is installed. Platforms register the component and consume the crypto functionality through [`service`].
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
#![cfg_attr(all(not(feature = "std"), not(test), not(feature = "mockall")), no_std)]
#![deny(missing_docs)]
#![cfg_attr(coverage, feature(coverage_attribute))]

extern crate alloc;

pub mod component;
pub mod error;
mod integration_test;
mod one_crypto;
pub mod service;
