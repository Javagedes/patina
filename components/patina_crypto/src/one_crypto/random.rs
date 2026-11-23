//! [`Random`] implementation.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use super::{OneCrypto, ensure, optional_slice, protocol_fn};
use crate::{error::Result, service::random::Random};

impl Random for OneCrypto {
    fn seed(&self, seed: Option<&[u8]>) -> Result<()> {
        let random_seed = protocol_fn!(self, random_seed);
        let (seed, seed_size) = optional_slice(seed);
        // SAFETY: `seed` is null or valid for `seed_size` bytes.
        ensure(unsafe { random_seed(seed, seed_size) })
    }

    fn fill_bytes(&self, output: &mut [u8]) -> Result<()> {
        let random_bytes = protocol_fn!(self, random_bytes);
        // SAFETY: `output` is writable for its length.
        ensure(unsafe { random_bytes(output.as_mut_ptr(), output.len()) })
    }
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
mod tests {
    use patina::standard::efi;

    use super::{
        super::{protocol::OneCryptoProtocol, test_support::*},
        *,
    };
    use crate::error::CryptoError;

    extern "efiapi" fn random_seed(seed: *const u8, size: usize) -> efi::Boolean {
        boolean(seed.is_null() == (size == 0))
    }
    extern "efiapi" fn random_bytes(output: *mut u8, size: usize) -> efi::Boolean {
        // SAFETY: `output` is writable for `size` bytes.
        unsafe { output.write_bytes(0xa5, size) };
        boolean(true)
    }

    #[test]
    fn test_one_crypto_random() {
        let crypto = crypto(OneCryptoProtocol {
            random_seed: Some(random_seed),
            random_bytes: Some(random_bytes),
            ..protocol()
        });
        assert_eq!(crypto.seed(None), Ok(()));
        assert_eq!(crypto.seed(Some(&[1, 2])), Ok(()));
        let mut output = [0u8; 3];
        crypto.fill_bytes(&mut output).expect("random");
        assert_eq!(output, [0xa5; 3]);
        assert_eq!(super::super::test_support::crypto(protocol()).seed(None), Err(CryptoError::Unsupported));
    }
}
