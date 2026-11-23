//! Image authorization with revoke-list precedence and verified-chain revocation.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use crate::{
    database::{SignatureDatabase, SignatureEntry, SignatureKind},
    image::AuthenticodeImage,
};
use alloc::vec::Vec;
use patina::crypto::{
    error::{CryptoError, Result},
    hash::{Hash, HashAlgorithm},
    signature::{Signature, SignatureAlgorithm},
};

fn entries(bytes: &[u8], revoke: bool) -> Result<Vec<SignatureEntry<'_>>> {
    let mut entries = Vec::new();
    for list in SignatureDatabase::new(bytes) {
        let list = match list {
            Ok(list) => list,
            Err(error) => {
                log::warn!("Malformed {} signature database: {error}", if revoke { "dbx" } else { "db" });
                if revoke {
                    return Err(CryptoError::VerificationFailed);
                }

                break;
            }
        };
        for entry in list.entries() {
            match entry {
                Ok(entry) => entries.push(entry),
                Err(error) => {
                    log::warn!("Malformed {} signature entry: {error}", if revoke { "dbx" } else { "db" });
                    if revoke {
                        return Err(CryptoError::VerificationFailed);
                    }
                    break;
                }
            }
        }
    }
    Ok(entries)
}

fn image_hash_matches(
    image: &mut AuthenticodeImage<'_>,
    hash: &dyn Hash,
    entries: &[SignatureEntry<'_>],
    revoke: bool,
) -> Result<bool> {
    for entry in entries {
        let SignatureKind::ImageHash(algorithm) = entry.format.kind else { continue };
        match image.digest(hash, algorithm) {
            Ok(digest) if digest == entry.data => return Ok(true),
            Ok(_) => {}
            Err(error) => {
                log::warn!(
                    "Unable to hash image with {algorithm:?} for {}: {error}",
                    if revoke { "dbx" } else { "db" }
                );
                if revoke {
                    return Err(error);
                }
            }
        }
    }
    Ok(false)
}

fn chain_revoked(
    chain: &[Vec<u8>],
    revoked: &[SignatureEntry<'_>],
    hash: &dyn Hash,
    signature: &dyn Signature,
) -> Result<bool> {
    if chain.is_empty() {
        log::warn!("Authenticode provider did not return a verified certificate chain");
        return Ok(true);
    }
    if revoked.is_empty() {
        return Ok(false);
    }
    let has_certificate_hashes =
        revoked.iter().any(|entry| matches!(entry.format.kind, SignatureKind::CertificateHash(_)));
    for certificate in chain {
        if revoked.iter().any(|entry| entry.format.kind == SignatureKind::Certificate && entry.data == certificate) {
            return Ok(true);
        }
        if !has_certificate_hashes {
            continue;
        }
        let tbs = signature.tbs_certificate(certificate)?;
        let mut digests = Vec::new();
        for entry in revoked {
            let SignatureKind::CertificateHash(algorithm) = entry.format.kind else { continue };
            let digest = if let Some((_, digest)) = digests.iter().find(|(kind, _)| *kind == algorithm) {
                digest
            } else {
                let digest = hash.hash_all(algorithm, &tbs)?;
                if digest.len() != algorithm.digest_size() {
                    return Err(CryptoError::Failed);
                }
                digests.push((algorithm, digest));
                &digests.last().expect("digest was just inserted").1
            };
            if entry.certificate_digest() == Some(digest.as_slice()) {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

/// Returns the V1 signature-data authority to measure, or `None` for hash authorization.
pub(crate) fn verify(
    bytes: &[u8],
    db: &[u8],
    dbx: &[u8],
    hash: &dyn Hash,
    signature: &dyn Signature,
) -> Result<Option<Vec<u8>>> {
    let mut image = AuthenticodeImage::parse(bytes)?;
    let revoked = entries(dbx, true)?;
    if image_hash_matches(&mut image, hash, &revoked, true)? {
        log::warn!("Secure Boot rejected an image digest enrolled in dbx");
        return Err(CryptoError::VerificationFailed);
    }
    let allowed = entries(db, false)?;
    if image_hash_matches(&mut image, hash, &allowed, false)? {
        return Ok(None);
    }
    // Collect only borrowed signature slices, so hashing can mutably update the digest cache.
    let signatures: Vec<_> = image.signatures().collect();
    for signed_data in signatures {
        let algorithm = match signature.authenticode_hash_algorithm(signed_data) {
            Ok(algorithm) => algorithm,
            Err(error) => {
                log::debug!("Unusable Authenticode signature: {error}");
                continue;
            }
        };
        if !matches!(algorithm, HashAlgorithm::Sha256 | HashAlgorithm::Sha384 | HashAlgorithm::Sha512) {
            log::debug!("Unsupported Secure Boot signature digest algorithm: {algorithm:?}");
            continue;
        }
        let digest = match image.digest(hash, algorithm) {
            Ok(digest) => digest,
            Err(error) => {
                log::warn!("Unable to hash Authenticode image with {algorithm:?}: {error}");
                continue;
            }
        };
        for entry in &allowed {
            let certificate = match entry.format.kind {
                SignatureKind::Certificate => entry.data.to_vec(),
                SignatureKind::CertificateHash(_) => {
                    let Some(digest) = entry.certificate_digest() else { continue };
                    match signature.trust_anchor(digest, signed_data) {
                        Ok(certificate) => certificate,
                        Err(error) => {
                            log::debug!("Unable to resolve Authenticode trust anchor: {error}");
                            continue;
                        }
                    }
                }
                _ => continue,
            };
            let result = signature
                .new_verifier(SignatureAlgorithm::Authenticode, &certificate)
                .and_then(|verifier| verifier.verify(digest, signed_data));
            let verified = match result {
                Ok(verified) => verified,
                Err(error) => {
                    log::debug!("Authenticode trust anchor did not authorize image: {error}");
                    continue;
                }
            };
            match chain_revoked(&verified.signer_chain, &revoked, hash, signature) {
                Ok(false) => {
                    let mut authority = entry.owner.copied().unwrap_or([0; 16]).to_vec();
                    authority.extend_from_slice(&certificate);
                    return Ok(Some(authority));
                }
                Ok(true) => log::debug!("Authenticode verified chain is revoked or unavailable"),
                Err(error) => log::warn!("Unable to check Authenticode chain revocation: {error}"),
            }
        }
    }
    Err(CryptoError::VerificationFailed)
}

#[cfg(test)]
#[cfg_attr(coverage, coverage(off))]
#[path = "verification_tests.rs"]
mod tests;
