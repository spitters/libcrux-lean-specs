//! Differential tests: compare our pure specs against libcrux reference implementations.
//!
//! Level 1 verification: for random inputs, our specs compute the same functions
//! as the corresponding libcrux crates.

use proptest::prelude::*;

// Helper: generate a random [u8; 12] for nonces
fn arb_nonce() -> impl Strategy<Value = [u8; 12]> {
    prop::array::uniform12(any::<u8>())
}

// --- SHA-256 ---

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    #[test]
    fn sha256_differential(msg in proptest::collection::vec(any::<u8>(), 0..256)) {
        let ours = libcrux_specs::sha256::sha256(&msg);
        let theirs = libcrux_sha2::sha256(&msg);
        prop_assert_eq!(ours, theirs, "SHA-256 mismatch on {} bytes", msg.len());
    }
}

#[test]
fn sha256_empty() {
    let ours = libcrux_specs::sha256::sha256(&[]);
    let theirs = libcrux_sha2::sha256(&[]);
    assert_eq!(ours, theirs);
}

// --- HMAC-SHA256 ---

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    #[test]
    fn hmac_sha256_differential(
        key in proptest::collection::vec(any::<u8>(), 0..128),
        msg in proptest::collection::vec(any::<u8>(), 0..256),
    ) {
        let ours = libcrux_specs::hmac::hmac_sha256(&key, &msg);
        let theirs = libcrux_hmac::hmac(
            libcrux_hmac::Algorithm::Sha256,
            &key,
            &msg,
            None,
        );
        let theirs_arr: [u8; 32] = theirs.try_into().expect("HMAC output should be 32 bytes");
        prop_assert_eq!(ours, theirs_arr, "HMAC-SHA256 mismatch");
    }
}

// --- HKDF ---

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    #[test]
    fn hkdf_extract_differential(
        salt in proptest::collection::vec(any::<u8>(), 1..64),
        ikm in proptest::collection::vec(any::<u8>(), 1..64),
    ) {
        let ours = libcrux_specs::hkdf::hkdf_extract(&salt, &ikm);
        let mut theirs = [0u8; 32];
        libcrux_hkdf::extract(
            libcrux_hkdf::Algorithm::Sha256,
            &mut theirs,
            &salt,
            &ikm,
        ).expect("HKDF extract should not fail");
        prop_assert_eq!(ours, theirs, "HKDF-Extract mismatch");
    }

    #[test]
    fn hkdf_expand_differential(
        prk in prop::array::uniform32(any::<u8>()),
        info in proptest::collection::vec(any::<u8>(), 0..64),
        len in 1usize..=255,
    ) {
        let len = len.min(32 * 255);
        let ours = libcrux_specs::hkdf::hkdf_expand(&prk, &info, len);
        let mut theirs = vec![0u8; len];
        let result = libcrux_hkdf::expand(
            libcrux_hkdf::Algorithm::Sha256,
            &mut theirs,
            &prk,
            &info,
        );
        if result.is_ok() {
            prop_assert_eq!(ours.len(), theirs.len(), "HKDF-Expand length mismatch");
            prop_assert_eq!(ours, theirs, "HKDF-Expand mismatch for len={}", len);
        }
    }
}

// --- AES-128 (block cipher via RustCrypto) ---

mod aes_block {
    use super::*;
    use aes::cipher::{BlockEncrypt, KeyInit};
    use aes::cipher::generic_array::GenericArray;
    use aes::Aes128;

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(1000))]

        #[test]
        fn aes128_differential(
            key in prop::array::uniform16(any::<u8>()),
            pt in prop::array::uniform16(any::<u8>()),
        ) {
            let ours = libcrux_specs::aes::aes128_encrypt(key, pt);

            let cipher = Aes128::new(GenericArray::from_slice(&key));
            let mut block = GenericArray::clone_from_slice(&pt);
            cipher.encrypt_block(&mut block);
            let theirs: [u8; 16] = block.into();

            prop_assert_eq!(ours, theirs, "AES-128 mismatch");
        }
    }
}

// --- AES-128-GCM ---

mod aes_gcm_tests {
    use super::*;
    #[allow(unused_imports)]
    use libcrux_aesgcm::AeadConsts as _;

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(200))]

        #[test]
        fn aes128_gcm_seal_differential(
            key in prop::array::uniform16(any::<u8>()),
            nonce in arb_nonce(),
            aad in proptest::collection::vec(any::<u8>(), 0..64),
            pt in proptest::collection::vec(any::<u8>(), 0..128),
        ) {
            // Our implementation
            let (our_ct, our_tag) = libcrux_specs::aes_gcm::aes128_gcm_encrypt(&key, &nonce, &aad, &pt);

            // libcrux-aesgcm: typed key API
            let k: libcrux_aesgcm::AesGcm128Key = key.into();
            let n: libcrux_aesgcm::AesGcm128Nonce = nonce.into();
            let mut their_ct = vec![0u8; pt.len()];
            let mut their_tag: libcrux_aesgcm::AesGcm128Tag = [0u8; 16].into();
            k.encrypt(&mut their_ct, &mut their_tag, &n, &aad, &pt)
                .expect("AES-GCM encrypt should not fail");

            prop_assert_eq!(&our_ct[..], &their_ct[..], "AES-128-GCM ciphertext mismatch");
            let their_tag_bytes: &[u8] = their_tag.as_ref();
            prop_assert_eq!(&our_tag[..], &their_tag_bytes[..16], "AES-128-GCM tag mismatch");
        }
    }
}

// --- X25519 ---

mod x25519_tests {
    use super::*;

    fn clamp_scalar(k: &mut [u8; 32]) {
        k[0] &= 248;
        k[31] &= 127;
        k[31] |= 64;
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(200))]

        #[test]
        fn x25519_base_differential(mut sk in prop::array::uniform32(any::<u8>())) {
            clamp_scalar(&mut sk);

            let ours = libcrux_specs::curve25519::x25519_base(&sk);

            let mut theirs = [0u8; 32];
            libcrux_curve25519::secret_to_public(&mut theirs, &sk);

            prop_assert_eq!(ours, theirs, "X25519 base point mismatch");
        }

        #[test]
        fn x25519_scalarmult_differential(
            mut sk in prop::array::uniform32(any::<u8>()),
            mut pk_seed in prop::array::uniform32(any::<u8>()),
        ) {
            clamp_scalar(&mut sk);
            clamp_scalar(&mut pk_seed);

            // Derive a valid public key
            let mut valid_pk = [0u8; 32];
            libcrux_curve25519::secret_to_public(&mut valid_pk, &pk_seed);

            let ours = libcrux_specs::curve25519::x25519_scalarmult(&sk, &valid_pk);

            let mut theirs = [0u8; 32];
            let _ = libcrux_curve25519::ecdh(&mut theirs, &valid_pk, &sk);

            prop_assert_eq!(ours, theirs, "X25519 scalar mult mismatch");
        }
    }
}

// --- ChaCha20-Poly1305 ---

mod chacha20poly1305_tests {
    use super::*;

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(200))]

        #[test]
        fn chacha20poly1305_encrypt_differential(
            key in prop::array::uniform32(any::<u8>()),
            nonce in arb_nonce(),
            aad in proptest::collection::vec(any::<u8>(), 0..64),
            msg in proptest::collection::vec(any::<u8>(), 1..128),
        ) {
            let (our_ct, our_tag) = libcrux_specs::chacha20poly1305::chacha20_poly1305_encrypt(
                &key, &nonce, &aad, &msg,
            );

            // libcrux reference: encrypt_detached(key, ptxt, ctxt, tag, aad, nonce)
            let mut their_ct = vec![0u8; msg.len()];
            let mut their_tag = [0u8; 16];
            libcrux_chacha20poly1305::encrypt_detached(
                &key, &msg, &mut their_ct, &mut their_tag, &aad, &nonce,
            ).expect("ChaCha20Poly1305 encrypt failed");

            prop_assert_eq!(&our_ct[..], &their_ct[..], "ChaCha20-Poly1305 ct mismatch");
            prop_assert_eq!(&our_tag[..], &their_tag[..], "ChaCha20-Poly1305 tag mismatch");
        }
    }
}

// --- Ed25519 (roundtrip only — no libcrux reference dependency downloaded) ---

mod ed25519_tests {
    use super::*;

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(100))]

        #[test]
        fn ed25519_sign_verify_roundtrip(
            sk in prop::array::uniform32(any::<u8>()),
            msg in proptest::collection::vec(any::<u8>(), 0..128),
        ) {
            let pk = libcrux_specs::ed25519::ed25519_public_key(&sk);
            let sig = libcrux_specs::ed25519::ed25519_sign(&sk, &msg);
            let valid = libcrux_specs::ed25519::ed25519_verify(&pk, &msg, &sig);
            prop_assert!(valid, "Ed25519 sign/verify roundtrip failed");
        }
    }
}

// --- Fixed-length wrappers (SSProve bridge) ---

mod fixed_tests {
    use super::*;

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(500))]

        #[test]
        fn fixed_sha256_32(msg in prop::array::uniform32(any::<u8>())) {
            let ours = libcrux_specs::fixed::sha256_32(&msg);
            let theirs = libcrux_sha2::sha256(&msg);
            prop_assert_eq!(ours, theirs, "fixed::sha256_32 mismatch");
        }

        #[test]
        fn fixed_hmac_sha256_32(
            key in prop::array::uniform32(any::<u8>()),
            msg in prop::array::uniform32(any::<u8>()),
        ) {
            let ours = libcrux_specs::fixed::hmac_sha256_32(&key, &msg);
            let theirs = libcrux_hmac::hmac(
                libcrux_hmac::Algorithm::Sha256,
                &key,
                &msg,
                None,
            );
            let theirs_arr: [u8; 32] = theirs.try_into().unwrap();
            prop_assert_eq!(ours, theirs_arr, "fixed::hmac_sha256_32 mismatch");
        }

        #[test]
        fn fixed_hkdf_extract_32(
            salt in prop::array::uniform32(any::<u8>()),
            ikm in prop::array::uniform32(any::<u8>()),
        ) {
            let ours = libcrux_specs::fixed::hkdf_extract_32(&salt, &ikm);
            let mut theirs = [0u8; 32];
            libcrux_hkdf::extract(
                libcrux_hkdf::Algorithm::Sha256,
                &mut theirs,
                &salt,
                &ikm,
            ).unwrap();
            prop_assert_eq!(ours, theirs, "fixed::hkdf_extract_32 mismatch");
        }

        #[test]
        fn fixed_hkdf_expand_32(
            prk in prop::array::uniform32(any::<u8>()),
            info in prop::array::uniform32(any::<u8>()),
        ) {
            let ours = libcrux_specs::fixed::hkdf_expand_32(&prk, &info);
            let mut theirs = [0u8; 32];
            libcrux_hkdf::expand(
                libcrux_hkdf::Algorithm::Sha256,
                &mut theirs,
                &prk,
                &info,
            ).unwrap();
            prop_assert_eq!(ours, theirs, "fixed::hkdf_expand_32 mismatch");
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(100))]

        #[test]
        fn fixed_x25519_scalarmult(
            mut sk in prop::array::uniform32(any::<u8>()),
            mut pk_sk in prop::array::uniform32(any::<u8>()),
        ) {
            sk[0] &= 248; sk[31] &= 127; sk[31] |= 64;
            pk_sk[0] &= 248; pk_sk[31] &= 127; pk_sk[31] |= 64;

            let mut valid_pk = [0u8; 32];
            libcrux_curve25519::secret_to_public(&mut valid_pk, &pk_sk);

            let ours = libcrux_specs::fixed::x25519_scalarmult(&sk, &valid_pk);

            let mut theirs = [0u8; 32];
            let _ = libcrux_curve25519::ecdh(&mut theirs, &valid_pk, &sk);

            prop_assert_eq!(ours, theirs, "fixed::x25519_scalarmult mismatch");
        }

        #[test]
        fn fixed_x25519_base(mut sk in prop::array::uniform32(any::<u8>())) {
            sk[0] &= 248; sk[31] &= 127; sk[31] |= 64;

            let ours = libcrux_specs::fixed::x25519_base(&sk);

            let mut theirs = [0u8; 32];
            libcrux_curve25519::secret_to_public(&mut theirs, &sk);

            prop_assert_eq!(ours, theirs, "fixed::x25519_base mismatch");
        }
    }
}

// --- Known Answer Tests (NIST / RFC vectors) ---

#[test]
fn sha256_nist_vector() {
    // SHA-256("abc") from FIPS 180-4
    let expected = hex::decode(
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    ).unwrap();
    let result = libcrux_specs::sha256::sha256(b"abc");
    assert_eq!(&result[..], &expected[..]);
}

#[test]
fn hmac_sha256_rfc4231_test1() {
    // RFC 4231 Test Case 1
    let key = hex::decode("0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b").unwrap();
    let data = b"Hi There";
    let expected = hex::decode(
        "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"
    ).unwrap();
    let result = libcrux_specs::hmac::hmac_sha256(&key, data);
    assert_eq!(&result[..], &expected[..]);
}

#[test]
fn hkdf_rfc5869_test1() {
    // RFC 5869 Test Case 1 (SHA-256)
    let ikm = hex::decode("0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b").unwrap();
    let salt = hex::decode("000102030405060708090a0b0c").unwrap();
    let info = hex::decode("f0f1f2f3f4f5f6f7f8f9").unwrap();

    let prk = libcrux_specs::hkdf::hkdf_extract(&salt, &ikm);
    let expected_prk = hex::decode(
        "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5"
    ).unwrap();
    assert_eq!(&prk[..], &expected_prk[..], "HKDF-Extract PRK mismatch");

    let okm = libcrux_specs::hkdf::hkdf_expand(&prk, &info, 42);
    let expected_okm = hex::decode(
        "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865"
    ).unwrap();
    assert_eq!(&okm[..], &expected_okm[..], "HKDF-Expand OKM mismatch");
}

#[test]
fn aes128_nist_vector() {
    // NIST AES-128 test vector (FIPS 197 Appendix B)
    let key: [u8; 16] = hex::decode("2b7e151628aed2a6abf7158809cf4f3c")
        .unwrap().try_into().unwrap();
    let pt: [u8; 16] = hex::decode("3243f6a8885a308d313198a2e0370734")
        .unwrap().try_into().unwrap();
    let expected: [u8; 16] = hex::decode("3925841d02dc09fbdc118597196a0b32")
        .unwrap().try_into().unwrap();
    let result = libcrux_specs::aes::aes128_encrypt(key, pt);
    assert_eq!(result, expected, "AES-128 NIST vector mismatch");
}

#[test]
fn x25519_rfc7748_vector() {
    // RFC 7748 Section 6.1: Alice's private key and public key
    let alice_sk: [u8; 32] = hex::decode(
        "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a"
    ).unwrap().try_into().unwrap();
    let expected_pk: [u8; 32] = hex::decode(
        "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a"
    ).unwrap().try_into().unwrap();
    let result = libcrux_specs::curve25519::x25519_base(&alice_sk);
    assert_eq!(result, expected_pk, "X25519 RFC 7748 vector mismatch");
}
