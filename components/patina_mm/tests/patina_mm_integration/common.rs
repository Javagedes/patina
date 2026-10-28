//! Common Test Infrastructure for Patina MM Integration Tests
//!
//! This module provides shared test infrastructure, constants, and utilities
//! used across all MM integration tests.
//!
//! ## License
//!
//! Copyright (C) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0

pub mod constants;
pub mod framework;
pub mod handlers;
pub mod message_parser;
pub mod real_component_framework;

// Re-export commonly used items for test infrastructure
pub use constants::*;
pub use framework::*;
pub use handlers::*;
pub use message_parser::*;
pub use real_component_framework::*;

pub fn mock_tpl_service()
-> patina::component::service::Service<dyn patina::component::service::uefi_services::tpl::TplServices> {
    use patina::component::service::{
        Service,
        uefi_services::tpl::{MockTplServices, PreviousTpl},
    };
    let mut tpl = MockTplServices::new();
    tpl.expect_raise_tpl().returning(|_| PreviousTpl::from_raw(4));
    tpl.expect_restore_tpl().returning(|_| ());
    Service::mock(Box::new(tpl))
}
