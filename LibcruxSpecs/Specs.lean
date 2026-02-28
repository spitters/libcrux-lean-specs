/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/

/-!
# libcrux-specs Extraction: Pure Crypto Function Signatures

Hand-transcribed type signatures from `libcrux/specs/libcrux-specs/src/`.
The Rust implementations are pure (no I/O, no panics for valid inputs),
so we model them as total Lean functions via `opaque` declarations.

## Source Files

| Module | Rust source | Main functions |
|--------|------------|----------------|
| SHA-256 | `sha256.rs` | `sha256` |
| HMAC | `hmac.rs` | `hmac_sha256` |
| HKDF | `hkdf.rs` | `hkdf_extract`, `hkdf_expand` |
| AES | `aes.rs` | `aes128_encrypt` |
| AES-GCM | `aes_gcm.rs` | `aes128_gcm_encrypt` |
| X25519 | `curve25519.rs` | `x25519_scalarmult`, `x25519_base` |
| P-256 | `p256.rs` | `scalar_mult`, `base_mult` |

## Design

Each Rust function is modeled as an `opaque` Lean constant. This is sound:
the Rust implementations are deterministic and total (for valid fixed-length
inputs), so they denote unique functions. We do NOT axiomatize any
properties except the standard cryptographic assumptions (PRF, CDH, IND-CPA).

Using `opaque` rather than `axiom` means these are genuine terms (not axioms
in `#print axioms`), but their bodies are sealed — we can't accidentally
unfold them and must rely on the bridge layer for all reasoning.

## Fixed-Length Convention

The Rust specs use mixed sizes (`[u8; 16]`, `[u8; 32]`, `&[u8]`).
We provide fixed-length wrappers at the 32-byte level.

## References

* `libcrux/specs/libcrux-specs/src/` — Rust source
-/

namespace LibcruxSpecs

/-! ## SHA-256 (sha256.rs) -/

/-- SHA-256 hash. Rust: `sha256(msg: &[u8]) -> [u8; 32]`.
    We model the fixed-length variant `sha256([u8; 32]) -> [u8; 32]`. -/
opaque sha256_32 : Vector UInt8 32 → Vector UInt8 32

/-! ## HMAC-SHA256 (hmac.rs) -/

/-- HMAC-SHA256. Rust: `hmac_sha256(key: &[u8], msg: &[u8]) -> [u8; 32]`.
    Fixed-length variant: both key and message are 32 bytes. -/
opaque hmac_sha256_32 : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-! ## HKDF-SHA256 (hkdf.rs) -/

/-- HKDF-Extract: `PRK = HMAC-SHA256(salt, IKM)`.
    Rust: `hkdf_extract(salt: &[u8], ikm: &[u8]) -> [u8; 32]`.
    Fixed-length: 32-byte salt, 32-byte IKM → 32-byte PRK.
    Specializes to non-empty salt case. -/
opaque hkdf_extract_32 : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-- HKDF-Expand (first 32 bytes): `T(1) = HMAC-SHA256(PRK, info || 0x01)`.
    Rust: `hkdf_expand(prk: &[u8; 32], info: &[u8], length: usize) -> Vec<u8>`.
    Fixed-length: 32-byte PRK, 32-byte info → first 32 bytes of OKM.
    This is sufficient for HPKE/EDHOC where we only need 32 bytes of output. -/
opaque hkdf_expand_32 : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-! ## AES-128 (aes.rs) -/

/-- AES-128 block encryption.
    Rust: `aes128_encrypt(key: [u8; 16], plaintext: [u8; 16]) -> [u8; 16]`. -/
opaque aes128_encrypt : Vector UInt8 16 → Vector UInt8 16 → Vector UInt8 16

/-! ## AES-128-GCM (aes_gcm.rs) -/

/-- AES-128-GCM authenticated encryption (simplified fixed-length model).
    In the real Rust spec, AES-GCM takes (key, nonce, aad, plaintext) and
    produces (ciphertext, tag). For the abstract AEAD bridge, we model the
    combined operation on fixed-length 32-byte buffers.

    Semantic interpretation: `aes128_gcm_seal(key, plaintext, aad)` = ciphertext,
    where the nonce is derived deterministically (or passed as part of the key). -/
opaque aes128_gcm_seal_32 : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-- AES-128-GCM authenticated decryption (simplified fixed-length model). -/
opaque aes128_gcm_open_32 : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-! ## X25519 (curve25519.rs) -/

/-- X25519 scalar multiplication (Diffie-Hellman operation).
    Rust: `x25519_scalarmult(k: &[u8; 32], u: &[u8; 32]) -> [u8; 32]`.
    Computes `k * u` on Curve25519. -/
opaque x25519_scalarmult : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-- X25519 base point multiplication: `k * 9` (the standard base point).
    Rust: `x25519_base(k: &[u8; 32]) -> [u8; 32]`.
    Used for key generation: `public_key = x25519_base(private_key)`. -/
opaque x25519_base : Vector UInt8 32 → Vector UInt8 32

/-! ## P-256 (p256.rs) -/

/-- P-256 scalar multiplication.
    Rust: `scalar_mult(k: &[u8; 32], p: &P256Point) -> P256Point`.
    We model the compressed form: 32-byte scalar × 32-byte point → 32-byte point.
    (In practice, the x-coordinate suffices for ECDH.) -/
opaque p256_scalar_mult_32 : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-- P-256 base point multiplication: `k * G`.
    Rust: `base_mult(k: &[u8; 32]) -> P256Point`.
    Compressed to 32-byte x-coordinate. -/
opaque p256_base_mult_32 : Vector UInt8 32 → Vector UInt8 32

end LibcruxSpecs
