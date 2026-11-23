//! Verification policy unit tests.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use super::*;
use crate::test_support::*;
use alloc::{boxed::Box, vec};
use patina::crypto::signature::{MockSignature, MockVerifier, VerifiedSignature};

fn signature(chain: Vec<Vec<u8>>) -> MockSignature {
    let mut signature = MockSignature::new();
    signature.expect_authenticode_hash_algorithm().returning(|_| Ok(patina::crypto::hash::HashAlgorithm::Sha256));
    signature.expect_new_verifier().returning(move |_, _| {
        let mut verifier = MockVerifier::new();
        let chain = chain.clone();
        verifier
            .expect_verify()
            .withf(|digest, signed_data| digest == [0xaa; 32] && signed_data == [1, 2, 3])
            .returning(move |_, _| Ok(VerifiedSignature::new(chain.clone())));
        Ok(Box::new(verifier))
    });
    signature
}

#[test]
fn test_secure_boot_verification_unsigned_hash_authorization() {
    let db = list(SHA256, &[0xaa; 32], false);
    assert_eq!(verify(&pe(false), &db, &[], &hash(), &MockSignature::new()), Ok(None));
    assert_eq!(verify(&pe(false), &[], &[], &hash(), &MockSignature::new()), Err(CryptoError::VerificationFailed));
}

#[test]
fn test_secure_boot_verification_dbx_precedes_db() {
    let db = list(SHA256, &[0xaa; 32], false);
    assert_eq!(verify(&pe(true), &db, &db, &hash(), &MockSignature::new()), Err(CryptoError::VerificationFailed));
    let mut corrupt = list(SHA256, &[0xbb; 32], false);
    corrupt.push(0);
    assert_eq!(verify(&pe(false), &db, &corrupt, &hash(), &MockSignature::new()), Err(CryptoError::VerificationFailed));
}

#[test]
fn test_secure_boot_verification_db_valid_prefix() {
    let mut db = list(SHA256, &[0xaa; 32], false);
    db.extend([0; 3]);
    assert_eq!(verify(&pe(false), &db, &[], &hash(), &MockSignature::new()), Ok(None));
}

#[test]
fn test_secure_boot_verification_certificate_authority() {
    for (guid, v2) in [(X509, false), ("79518039-4715-4393-bdf8-d8e3c67fbac7", true)] {
        let db = list(guid, &[9, 8, 7], v2);
        let mut expected = vec![if v2 { 0 } else { 0x55 }; 16];
        expected.extend([9, 8, 7]);
        assert_eq!(verify(&pe(true), &db, &[], &hash(), &signature(vec![vec![9, 8, 7]])), Ok(Some(expected)));
    }
}

#[test]
fn test_secure_boot_verification_missing_or_revoked_chain() {
    let db = list(X509, &[9, 8, 7], false);
    assert_eq!(verify(&pe(true), &db, &[], &hash(), &signature(vec![])), Err(CryptoError::VerificationFailed));
    assert_eq!(
        verify(&pe(true), &db, &db, &hash(), &signature(vec![vec![9, 8, 7]])),
        Err(CryptoError::VerificationFailed)
    );
}

#[test]
fn test_secure_boot_verification_tbs_revocation_and_error() {
    let db = list(X509, &[9], false);
    let dbx = list(TBS256, &[0; 48], false);
    let mut signatures = signature(vec![vec![1]]);
    signatures.expect_tbs_certificate().returning(|_| Ok(vec![2]));
    let mut hash = hash();
    hash.expect_hash_all().returning(|_, _| Ok(vec![0; 32]));
    assert_eq!(verify(&pe(true), &db, &dbx, &hash, &signatures), Err(CryptoError::VerificationFailed));
    let mut signatures = signature(vec![vec![1]]);
    signatures.expect_tbs_certificate().returning(|_| Err(CryptoError::Failed));
    assert_eq!(verify(&pe(true), &db, &dbx, &hash, &signatures), Err(CryptoError::VerificationFailed));
}

#[test]
fn test_secure_boot_verification_tbs_anchor_resolution() {
    let db = list(TBS256, &[0; 48], false);
    let mut signature = signature(vec![vec![9]]);
    signature
        .expect_trust_anchor()
        .withf(|digest, data| digest == [0; 32] && data == [1, 2, 3])
        .once()
        .returning(|_, _| Ok(vec![9]));
    let result = verify(&pe(true), &db, &[], &hash(), &signature).unwrap().unwrap();
    assert_eq!(&result[16..], &[9]);
}

#[test]
fn test_secure_boot_verification_unsupported_dbx_hash_denies() {
    let dbx = list(SHA256, &[0xbb; 32], false);
    let mut hash = patina::crypto::hash::MockHash::new();
    hash.expect_new_hash().returning(|_| Err(CryptoError::Unsupported));
    assert_eq!(verify(&pe(false), &[], &dbx, &hash, &MockSignature::new()), Err(CryptoError::Unsupported));
}

#[test]
fn test_secure_boot_verification_unrevoked_chain_with_nonempty_dbx() {
    let db = list(X509, &[9], false);
    for dbx in [list(SHA256, &[0xbb; 32], false), list(X509, &[8], false)] {
        let authority = verify(&pe(true), &db, &dbx, &hash(), &signature(vec![vec![9]])).unwrap().unwrap();
        assert_eq!(&authority[16..], &[9]);
    }
}

#[test]
fn test_secure_boot_verification_crypto_failures_deny() {
    let db = list(X509, &[9], false);
    let mut signatures = MockSignature::new();
    signatures.expect_authenticode_hash_algorithm().returning(|_| Err(CryptoError::Unsupported));
    assert_eq!(verify(&pe(true), &db, &[], &hash(), &signatures), Err(CryptoError::VerificationFailed));

    let mut signatures = MockSignature::new();
    signatures.expect_authenticode_hash_algorithm().returning(|_| Ok(patina::crypto::hash::HashAlgorithm::Sha256));
    signatures.expect_new_verifier().returning(|_, _| {
        let mut verifier = MockVerifier::new();
        verifier.expect_verify().returning(|_, _| Err(CryptoError::VerificationFailed));
        Ok(Box::new(verifier))
    });
    assert_eq!(verify(&pe(true), &db, &[], &hash(), &signatures), Err(CryptoError::VerificationFailed));
}

#[test]
fn test_secure_boot_verification_failed_anchor_resolution_denies() {
    let db = list(TBS256, &[0; 48], false);
    let mut signatures = MockSignature::new();
    signatures.expect_authenticode_hash_algorithm().returning(|_| Ok(patina::crypto::hash::HashAlgorithm::Sha256));
    signatures.expect_trust_anchor().returning(|_, _| Err(CryptoError::NotFound));
    assert_eq!(verify(&pe(true), &db, &[], &hash(), &signatures), Err(CryptoError::VerificationFailed));
}

#[test]
fn test_secure_boot_verification_ignores_sha1_database_entries() {
    let sha1 = list("826ca512-cf10-4ac9-b187-be01496631bd", &[0xaa; 20], false);
    for signed in [false, true] {
        assert_eq!(verify(&pe(signed), &sha1, &[], &hash(), &signature(vec![])), Err(CryptoError::VerificationFailed));
        let db = list(SHA256, &[0xaa; 32], false);
        assert_eq!(verify(&pe(signed), &db, &sha1, &hash(), &MockSignature::new()), Ok(None));
    }
}

#[test]
fn test_secure_boot_verification_rejects_sha1_signature_digest() {
    let db = list(X509, &[9], false);
    let mut signatures = MockSignature::new();
    signatures.expect_authenticode_hash_algorithm().returning(|_| Ok(HashAlgorithm::Sha1));
    assert_eq!(verify(&pe(true), &db, &[], &hash(), &signatures), Err(CryptoError::VerificationFailed));
}
