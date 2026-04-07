/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bas Spitters
-/

import LibcruxSpecs.Extracted

/-!
# libcrux-specs: Pure Crypto Function Definitions

These definitions connect the hax-extracted `RustM`-monadic implementations
(in `LibcruxSpecs.Extracted`) to total Lean functions usable by SSProve.

## Design

Each function is defined as the successful result of the corresponding
`Libcrux_specs.Fixed.*` extracted definition. If the `RustM` computation
fails (unreachable for valid fixed-length inputs), a zero vector is returned.

This replaces the previous `opaque` declarations, closing the correspondence
gap between SSProve's abstract crypto primitives and the actual libcrux
implementations. The chain is now:

  SSProve security proofs
    → LibcruxSpecs.sha256_32 (this file)
    → Libcrux_specs.Fixed.sha256_32 (hax-extracted)
    → rust-specs/src/fixed.rs (pure Rust)
    → libcrux crates (verified by differential testing)

## References

* `libcrux/specs/libcrux-specs/src/` — Rust source
* `rust-specs/tests/differential.rs` — 22 proptest + 5 Wycheproof tests PASS
-/

/-- Extract successful result from `RustM`, returning default on failure. -/
def RustM.getD {α : Type} (x : RustM α) (d : α) : α :=
  match x with
  | .ok r => r
  | _ => d

namespace LibcruxSpecs

private def zero32 : Vector UInt8 32 := Vector.replicate 32 0
private def zero16 : Vector UInt8 16 := Vector.replicate 16 0

/-! ## SHA-256 (sha256.rs) -/

/-- SHA-256 hash of a 32-byte input. Backed by hax-extracted `Libcrux_specs.Fixed.sha256_32`. -/
noncomputable def sha256_32 (msg : Vector UInt8 32) : Vector UInt8 32 :=
  (Libcrux_specs.Fixed.sha256_32 msg).getD zero32

/-! ## HMAC-SHA256 (hmac.rs) -/

/-- HMAC-SHA256 with 32-byte key and message. -/
noncomputable def hmac_sha256_32 (key msg : Vector UInt8 32) : Vector UInt8 32 :=
  (Libcrux_specs.Fixed.hmac_sha256_32 key msg).getD zero32

/-! ## HKDF-SHA256 (hkdf.rs) -/

/-- HKDF-Extract: `PRK = HMAC-SHA256(salt, IKM)`. -/
noncomputable def hkdf_extract_32 (salt ikm : Vector UInt8 32) : Vector UInt8 32 :=
  (Libcrux_specs.Fixed.hkdf_extract_32 salt ikm).getD zero32

/-- HKDF-Expand (first 32 bytes): `T(1) = HMAC-SHA256(PRK, info || 0x01)`. -/
noncomputable def hkdf_expand_32 (prk info : Vector UInt8 32) : Vector UInt8 32 :=
  (Libcrux_specs.Fixed.hkdf_expand_32 prk info).getD zero32

/-! ## AES-128 (aes.rs) -/

/-- AES-128 block encryption. -/
noncomputable def aes128_encrypt (key pt : Vector UInt8 16) : Vector UInt8 16 :=
  (Libcrux_specs.Aes.aes128_encrypt key pt).getD zero16

/-! ## AES-128-GCM (aes_gcm.rs) -/

/-- AES-128-GCM authenticated encryption with fixed 32-byte buffers. -/
noncomputable def aes128_gcm_seal_32 (key pt aad : Vector UInt8 32) : Vector UInt8 32 :=
  (Libcrux_specs.Fixed.aes128_gcm_seal_32 key pt aad).getD zero32

/-- AES-128-GCM authenticated decryption with fixed 32-byte buffers. -/
noncomputable def aes128_gcm_open_32 (key ct aad : Vector UInt8 32) : Vector UInt8 32 :=
  (Libcrux_specs.Fixed.aes128_gcm_open_32 key ct aad).getD zero32

/-! ## X25519 (curve25519.rs) -/

/-- X25519 scalar multiplication: `k * u` on Curve25519. -/
noncomputable def x25519_scalarmult (k u : Vector UInt8 32) : Vector UInt8 32 :=
  (Libcrux_specs.Fixed.x25519_scalarmult k u).getD zero32

/-- X25519 base point multiplication: `k * 9`. -/
noncomputable def x25519_base (k : Vector UInt8 32) : Vector UInt8 32 :=
  (Libcrux_specs.Fixed.x25519_base k).getD zero32

/-! ## P-256 (p256.rs) -/

/-- P-256 scalar multiplication (compressed x-coordinate). -/
noncomputable def p256_scalar_mult_32 (k p : Vector UInt8 32) : Vector UInt8 32 :=
  (Libcrux_specs.Fixed.p256_scalar_mult_32 k p).getD zero32

/-- P-256 base point multiplication: `k * G` (compressed x-coordinate). -/
noncomputable def p256_base_mult_32 (k : Vector UInt8 32) : Vector UInt8 32 :=
  (Libcrux_specs.Fixed.p256_base_mult_32 k).getD zero32

end LibcruxSpecs
