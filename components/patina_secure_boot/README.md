# Patina Secure Boot

`patina_secure_boot` registers a native image-security handler with the Patina DXE
core. It consumes `patina::crypto::hash::Hash` and
`patina::crypto::signature::Signature`; it does not depend on a particular crypto
provider or on another component crate.

Register `component::SecureBootComponent::new()` alongside a crypto provider such
as `patina_crypto::component::OneCryptoComponent::new()`.

## Verification

- Firmware-volume images bypass this handler. The loader supplies the origin
  classification; a device path claiming to be an FV is not sufficient.
- Other images are checked when the global `SecureBoot` variable equals one.
  An absent variable means disabled. Malformed values and variable-service errors
  deny loading.
- `dbx` image hashes take precedence over both authorization paths.
- `db` can authorize an unsigned or signed image by its Authenticode digest.
- Otherwise, embedded Authenticode signatures are verified against X.509 or
  TBSCertificate-hash trust anchors in `db`. Every certificate in the returned,
  verified chain is checked against `dbx`.
- Legacy and V2 signature-list encodings are supported. Database wire types use
  `zerocopy` without assuming buffer alignment.
- Image and certificate-hash entries support SHA-256, SHA-384, and SHA-512.
  SHA-1 database entries are ignored, and SHA-1 Authenticode signatures do not
  authorize an image, matching the reference verification library.
- Malformed revoke-lists and failures computing their supported digests fail
  closed. Allow-list parsing preserves valid entries before a malformed entry
  and continues with subsequent complete lists when possible.
- Certificate-hash revocations are unconditional, including legacy entries with
  a nonzero revocation time, matching the reference library's chain checks.
- Goblin parses PE32/PE32+ headers and section tables. Hashing streams the
  Authenticode regions through the crypto service, without allocating a second
  image. Overlapping sections, out-of-bounds data, and certificate tables not at
  the end of the file are rejected.

An accepted certificate authority is measured into PCR 7 through TCG2 as an
`EV_EFI_VARIABLE_AUTHORITY` event for `db`. Measurements are deduplicated for the
boot. Hash-authorized images do not measure an authority. Measurement errors are
logged and remain eligible for retry; like the reference `SecureBootHook`, they
do not overturn successful authorization.

## Integration requirements

The DXE core must provide `SecurityServices`. Native handlers run before the
existing architectural Security/Security2 protocols, and cannot override their
denials. Only images loaded after registration are covered; platform integration
must ensure the handler is registered before loading untrusted images.

The crypto provider must support the algorithms enrolled in `dbx`. Certificate
authorization also requires the Authenticode hash-algorithm query and a verified
signer-to-anchor chain. The OneCrypto V1 fallback that returns an empty chain is
not sufficient and fails closed.

Image-result tables and crypto-capability reporting are intentionally omitted.
This component does not implement authenticated variable updates, key enrollment,
or the variable driver's Secure Boot state machine.
