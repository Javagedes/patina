# Patina Crypto

`patina_crypto` defines Rust service interfaces for the cryptographic operations exposed by the EDK II
`BaseCryptLib` library (`CryptoPkg/Include/Library/BaseCryptLib.h`). The interfaces keep the same feature set but use
Rust semantics:

- Buffer + size pairs are slices (`&[u8]`); variable sized outputs are returned as `Vec<u8>`.
- `BOOLEAN`/`EFI_STATUS` results are `Result<T, CryptoError>`. Failed verifications return
  `CryptoError::VerificationFailed`.
- Each capability is algorithm agile. The algorithm and key are selected once through a single constructor (for
  example `Encryption::new_cipher(CipherAlgorithm::AesGcm, CipherKey::Symmetric(key))`), which returns a generic
  handle (`Cipher`) that works the same way for every algorithm. Functions that do the same job with different
  formats, such as `Pkcs1Verify`, `RsaPssVerify`, `EcDsaVerify`, `Pkcs7Verify`, `CmsVerify`, and
  `AuthenticodeVerify`, are a single `Verifier` selected by `SignatureAlgorithm`.
- `Hash` provides streaming (`new_hash`, `new_mac`) and one-shot (`hash_all`, `mac_all`) operations selected by
  algorithm enum. `EncryptionExt` and `SignatureExt` provide one-shot helpers on top of their handles.
- Handles are owned `Box<dyn ...>` trait objects that release their resources on `Drop`, so there are no
  `*New`/`*Free` pairs.
- Numeric identifiers (NIDs, GUIDs, digest lengths) are replaced with enums such as `HashAlgorithm`, `MacAlgorithm`,
  `KdfAlgorithm`, `SignatureAlgorithm`, and `Pkcs7Cipher`.

## Services

| Trait | Handle | `BaseCryptLib` functions |
| --- | --- | --- |
| `Hash` | `DigestContext` | SHA-1/256/384/512 hashing, HMAC-SHA256/384, PBKDF2, HKDF |
| `Encryption` / `EncryptionExt` | `Cipher` | AES-CBC, AES-GCM (tag appended), RSA-OAEP, PKCS#7 enveloped data |
| `Signature` / `SignatureExt` | `Signer` / `Verifier` | RSA PKCS#1 v1.5 and PSS, ECDSA, PKCS#7, CMS, Authenticode signing and verification; X.509 certificate parsing, verification, and chain handling; PKCS#7 signer and certificate extraction, EKU verification; Authenticode trust anchor lookup and RFC 3161 timestamp verification; ASN.1 tag lookup |
| `Random` | | Random number generation |

```rust
use patina::component::service::Service;
use patina_crypto::{
    error::Result,
    service::{
        encryption::{CipherAlgorithm, CipherKey, Encryption},
        hash::HashAlgorithm,
        signature::{Signature, SignatureAlgorithm, SignatureExt},
    },
};

fn example(
    encryption: Service<dyn Encryption>,
    signature: Service<dyn Signature>,
    key: &[u8],
    certificate: &[u8],
    message: &[u8],
    message_signature: &[u8],
) -> Result<Vec<u8>> {
    let algorithm = SignatureAlgorithm::RsaPss { digest: HashAlgorithm::Sha256, salt_size: 32 };
    signature.verify(algorithm, certificate, message, message_signature)?;

    let cipher = encryption.new_cipher(CipherAlgorithm::AesGcm, CipherKey::Symmetric(key))?;
    cipher.encrypt(&[0; 12], b"aad", message)
}
```

## Scope

These `BaseCryptLib` functions are intentionally excluded:

- MD5 and SM3 hashing (legacy algorithms).
- Raw `BigNum*`, `EcGroup*`, and `EcPoint*` math primitives.
- TLS (`TlsLib`).
- Diffie-Hellman and ECDH key agreement (`Dh*`, `EcGenerateKey`, `EcDhComputeKey`).
- Provider version and capability queries.
- `*GetContextSize`, `*Free`, and `X509ConstructCertificate*` helpers, which are replaced by owned Rust types.

## Implementations

### OneCrypto

The service interfaces and shared types live in `patina::crypto`, so consumers do not
depend on this provider component. The existing `patina_crypto::service` and
`patina_crypto::error` paths re-export the same SDK definitions for compatibility.

`OneCryptoComponent` produces every service from the `OneCrypto` protocol (`ONE_CRYPTO_PROTOCOL` version 1.x or
2.x, see `CryptoPkg/Library/BaseCryptLibOnOneCrypto`). It is dispatched once the protocol is installed. The implementation is
private to the crate: platforms only register the component, and consumers use the traits in `patina_crypto::service`.

```rust
use patina_crypto::component::OneCryptoComponent;

// Register with the DXE core alongside the platform's other components.
let component = OneCryptoComponent::new();
```

Notes on the implementation:

- Buffers the provider allocates are copied into Rust-owned values and released with `FreePool()`. Certificate
  lists from `Pkcs7GetSigners()` and `Pkcs7GetCertificatesList()` are released with `Pkcs7FreeSigners()`.
- Provider contexts (hash, HMAC, RSA, EC, trust anchor cache) are released when the Rust handle is dropped.
- RSA PKCS#1 v1.5 and ECDSA signers and verifiers hash the message with the selected digest; RSA-PSS hashes
  internally in the provider.
- CipherKey::PrivateKeyDer with RSA-OAEP is decrypt-only and uses SHA-1 (Pkcs1v2Decrypt).
- CMS and Authenticode signing are not provided by the protocol and report CryptoError::Unsupported.
- If AuthenticodeVerifyEx is unavailable, Authenticode verification falls back to AuthenticodeVerify and
  returns an empty signer chain.
- A protocol function that is `NULL` reports `CryptoError::Unsupported`.
- The protocol must have major version 1 or 2; any minor version is accepted. Version 2.0 appends functions to the
  version 1.0 table, so the bindings keep the version 1.0 table (`OneCryptoProtocol`) separate from the version 2.0
  table (`OneCryptoProtocolV2`). The version 2.0 table is only read when the provider reports major version 2, so
  a version 1 table is never accessed past its end.
- With a version 1 provider, the functions added in version 2.0 are unavailable: CMS verification, the
  Authenticode hash algorithm query, and trust anchor lookup report `CryptoError::Unsupported`; the CMS signer count
  is 0; no public key type is reported as supported; and Authenticode verification uses the `AuthenticodeVerify`
  fallback.
