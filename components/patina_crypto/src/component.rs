//! Component that produces the crypto services from the `OneCrypto` protocol.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use patina::{
    component::{
        component,
        params::Commands,
        protocol::Protocol,
        service::{Service, compat_memory::CompatMemoryManager},
    },
    error::Result,
};

use crate::one_crypto::{
    OneCrypto,
    protocol::{OneCryptoProtocol, OneCryptoProtocolV2},
};

/// Produces the [`crate::service`] services, backed by the `OneCrypto` protocol.
///
/// The component is dispatched once the `OneCrypto` protocol is installed. It registers an implementation of every
/// service in [`crate::service`]. Providers implementing protocol major version 1 or 2 are supported; with version 1,
/// functions added in version 2.0 are reported as unsupported.
#[derive(Debug, Default, Clone, Copy)]
pub struct OneCryptoComponent;

#[component]
impl OneCryptoComponent {
    /// Creates the component.
    pub const fn new() -> Self {
        Self
    }

    fn entry_point(
        self,
        protocol: Protocol<OneCryptoProtocol>,
        // Resolves the same protocol instance as `protocol`; it is only dereferenced for version 2 providers.
        protocol_v2: Protocol<OneCryptoProtocolV2>,
        memory: Service<dyn CompatMemoryManager>,
        mut commands: Commands,
    ) -> Result<()> {
        let one_crypto = OneCrypto::new(protocol, protocol_v2, memory)?;
        log::info!("OneCrypto crypto services installed (protocol version {}.{})", protocol.major, protocol.minor);
        commands.add_service(one_crypto);
        Ok(())
    }
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
mod tests {
    use alloc::boxed::Box;

    use patina::component::service::compat_memory::MockCompatMemoryManager;

    use super::*;
    use crate::one_crypto::{
        protocol::{ONE_CRYPTO_VERSION_MAJOR, ONE_CRYPTO_VERSION_MAJOR_MIN},
        test_support::mock_protocol,
    };

    fn run(protocol: OneCryptoProtocol) -> Result<()> {
        let memory = Service::mock(Box::new(MockCompatMemoryManager::new()) as Box<dyn CompatMemoryManager>);
        let (protocol, protocol_v2) = mock_protocol(protocol);
        OneCryptoComponent::new().entry_point(protocol, protocol_v2, memory, Commands::mock())
    }

    #[test]
    fn test_one_crypto_component_installs_services() {
        for major in ONE_CRYPTO_VERSION_MAJOR_MIN..=ONE_CRYPTO_VERSION_MAJOR {
            assert_eq!(run(OneCryptoProtocol { major, minor: 0, ..Default::default() }), Ok(()));
        }
    }

    #[test]
    fn test_one_crypto_component_rejects_incompatible_protocol() {
        let protocol = OneCryptoProtocol { major: ONE_CRYPTO_VERSION_MAJOR + 1, ..Default::default() };
        assert!(run(protocol).is_err());
    }
}
