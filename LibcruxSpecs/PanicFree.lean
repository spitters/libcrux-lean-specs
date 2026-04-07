/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bas Spitters
-/

import LibcruxSpecs.Specs
import LibcruxSpecs.PanicFreeInfra

/-!
# Panic-Freedom Predicates for LibcruxSpecs

This module defines `RustM.IsOk` predicates asserting that each extracted
crypto function succeeds (returns `.ok`, not `.fail` or `.div`) on all inputs.

## Design

Each predicate is stated as a `Prop` of the form:

```
∀ (inputs), (Libcrux_specs.Fixed.f inputs).isOk = true
```

These are currently `sorry`-ed: proving them requires showing that every
array index, integer operation, and loop iteration in the extracted code
is panic-free. The `native_panic_freedom` tactic (in `Hax.Tactic`) can
close some of these goals automatically for simpler functions.

## Why This Matters

`LibcruxSpecs.Specs` uses `RustM.getD` to unwrap extracted results, falling
back to a zero vector on failure. If a function actually panics, the spec
silently returns garbage. These predicates, once proved, guarantee that
the `getD` fallback is never reached, making the specs faithful.

## Verification Status

| Function | Rust proptest | Rust Kani | Lean `IsOk` |
|----------|:---:|:---:|:---:|
| `sha256_32` | 1000 | - | `sorry` |
| `hmac_sha256_32` | 500 + Wycheproof | - | `sorry` |
| `hkdf_extract_32` | 500 + Wycheproof | - | `sorry` |
| `hkdf_expand_32` | 500 | - | `sorry` |
| `aes128_encrypt` | 1000 + Wycheproof | VERIFIED | `sorry` |
| `aes128_gcm_seal_32` | 200 | - | `sorry` |
| `aes128_gcm_open_32` | 200 | - | `sorry` |
| `x25519_scalarmult` | 200 + Wycheproof | - | `sorry` |
| `x25519_base` | 200 | - | `sorry` |
| `p256_scalar_mult_32` | - | - | `sorry` |
| `p256_base_mult_32` | - | - | `sorry` |
-/

set_option autoImplicit false

/-! ## Helper: `RustM.IsOk` as a `Prop` -/

namespace RustM

/-- `RustM.IsOk x` holds when `x = .ok v` for some `v`. -/
def IsOk {α : Type} (x : RustM α) : Prop := x.isOk = true

/-- Extract the value from an `IsOk` computation. -/
noncomputable def getOk {α : Type} (x : RustM α) (h : IsOk x) : α :=
  x.of_isOk h

/-- When `IsOk` holds, `getD` returns the same value as `getOk`. -/
theorem getD_eq_getOk {α : Type} (x : RustM α) (d : α) (h : IsOk x) :
    x.getD d = x.getOk h := by
  unfold IsOk at h
  match x, h with
  | .ok v, _ => rfl

end RustM

namespace LibcruxSpecs.PanicFree

/-! ## Infrastructure: RustM.bind composition for IsOk -/

/-- If `x` succeeds and `f` succeeds on the result, then `x >>= f` succeeds. -/
theorem RustM.bind_isOk {α β : Type} (x : RustM α) (f : α → RustM β)
    (hx : x.isOk = true) (hf : ∀ a, x = .ok a → (f a).isOk = true) :
    (x >>= f).isOk = true := by
  match x, hx with
  | .ok v, _ => exact hf v rfl

/-- Variant: if `x` succeeds and `f` succeeds on ALL inputs, then `x >>= f` succeeds. -/
theorem RustM.bind_isOk' {α β : Type} (x : RustM α) (f : α → RustM β)
    (hx : x.isOk = true) (hf : ∀ a, (f a).isOk = true) :
    (x >>= f).isOk = true :=
  bind_isOk x f hx (fun a _ => hf a)

/-- `pure v` always succeeds. -/
@[simp] theorem RustM.pure_isOk {α : Type} (v : α) : (pure v : RustM α).isOk = true := rfl

/-! ## Panic-freedom predicates -/

/-- SHA-256 on 32-byte input does not panic. -/
theorem sha256_32_isOk (msg : Vector UInt8 32) :
    RustM.IsOk (Libcrux_specs.Fixed.sha256_32 msg) := by
  sorry

/-- HMAC-SHA256 on 32-byte key and message does not panic. -/
theorem hmac_sha256_32_isOk (key msg : Vector UInt8 32) :
    RustM.IsOk (Libcrux_specs.Fixed.hmac_sha256_32 key msg) := by
  sorry

/-- HKDF-Extract on 32-byte salt and IKM does not panic. -/
theorem hkdf_extract_32_isOk (salt ikm : Vector UInt8 32) :
    RustM.IsOk (Libcrux_specs.Fixed.hkdf_extract_32 salt ikm) := by
  sorry

/-- HKDF-Expand on 32-byte PRK and info does not panic. -/
theorem hkdf_expand_32_isOk (prk info : Vector UInt8 32) :
    RustM.IsOk (Libcrux_specs.Fixed.hkdf_expand_32 prk info) := by
  sorry

/-- Helper: AES-128 key expansion always succeeds. (Proof TODO) -/
theorem aes128_key_expand_isOk (key : Vector UInt8 16) :
    (Libcrux_specs.Aes.aes128_key_expand key).isOk = true := by
  sorry  -- TODO: deep proof through 2 nested while_loops + many array ops

/-- Helper: AES encryption rounds always succeed when given valid round_keys. (Proof TODO) -/
theorem aes_encrypt_rounds_isOk (pt : Vector UInt8 16)
    (round_keys : Array (Vector UInt8 16))
    (h : 11 ≤ round_keys.size) :
    (Libcrux_specs.Aes.aes_encrypt_rounds pt round_keys (10 : usize)).isOk = true := by
  sorry  -- TODO: deep proof through while_loop' + sub_bytes/shift_rows/mix_columns/add_round_key

open LibcruxSpecs.PanicFree in
/-- AES-128 block encryption does not panic.
    Compositional proof: depends on `aes128_key_expand_isOk` and
    `aes_encrypt_rounds_isOk` (the leaf functions, both still TODO).

    The `unsize` step preserves the size (11 round keys), which feeds into
    `aes_encrypt_rounds_isOk`'s precondition `11 ≤ slice.size`. -/
theorem aes128_encrypt_isOk (key pt : Vector UInt8 16) :
    RustM.IsOk (Libcrux_specs.Aes.aes128_encrypt key pt) := by
  unfold RustM.IsOk Libcrux_specs.Aes.aes128_encrypt
  -- Step 1: aes128_key_expand key
  apply LibcruxSpecs.PanicFree.bind_isOk_dep _ _ (aes128_key_expand_isOk key)
  intro round_keys _hke
  -- Step 2: unsize round_keys; result has size 11 (preserves Vector size)
  apply LibcruxSpecs.PanicFree.bind_isOk_dep _ _ (unsize_isOk round_keys)
  intro slice hsl
  -- After unsize: slice = round_keys.toArray, so slice.size = 11
  -- Step 3: aes_encrypt_rounds pt slice 10
  apply aes_encrypt_rounds_isOk
  -- Goal: 11 ≤ slice.size
  -- From hsl : Rust_primitives.unsize round_keys = .ok slice we get slice = round_keys.toArray
  unfold Rust_primitives.unsize at hsl
  simp at hsl
  rw [← hsl]
  simp [Vector.size_toArray]

/-- AES-128-GCM seal on 32-byte buffers does not panic. -/
theorem aes128_gcm_seal_32_isOk (key pt aad : Vector UInt8 32) :
    RustM.IsOk (Libcrux_specs.Fixed.aes128_gcm_seal_32 key pt aad) := by
  sorry

/-- AES-128-GCM open on 32-byte buffers does not panic. -/
theorem aes128_gcm_open_32_isOk (key ct aad : Vector UInt8 32) :
    RustM.IsOk (Libcrux_specs.Fixed.aes128_gcm_open_32 key ct aad) := by
  sorry

/-- Helper: Curve25519 internal scalar mult always succeeds.
    (Proof TODO — requires limb-bound invariants through Montgomery ladder.) -/
theorem curve25519_x25519_scalarmult_isOk (k u : Vector UInt8 32) :
    (Libcrux_specs.Curve25519.x25519_scalarmult k u).isOk = true := by
  sorry

/-- X25519 scalar multiplication does not panic.
    Trivial delegation to `Curve25519.x25519_scalarmult`. -/
theorem x25519_scalarmult_isOk (k u : Vector UInt8 32) :
    RustM.IsOk (Libcrux_specs.Fixed.x25519_scalarmult k u) := by
  unfold RustM.IsOk Libcrux_specs.Fixed.x25519_scalarmult
  exact curve25519_x25519_scalarmult_isOk k u

/-- X25519 base point multiplication does not panic.
    Compositional proof: `repeat 0 32 → set[0]:=9 → scalarmult k base`.
    Each step is shown to succeed using PanicFreeInfra lemmas. -/
theorem x25519_base_isOk (k : Vector UInt8 32) :
    RustM.IsOk (Libcrux_specs.Fixed.x25519_base k) := by
  unfold RustM.IsOk Libcrux_specs.Fixed.x25519_base Libcrux_specs.Curve25519.x25519_base
  -- Step 1: repeat (0 : u8) (32 : usize) — succeeds because size matches
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · exact LibcruxSpecs.PanicFree.repeat_isOk _ _ rfl
  intro base
  -- Step 2: update_at_usize base 0 9 — succeeds because 0 < 32
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · exact LibcruxSpecs.PanicFree.update_at_usize_isOk _ _ _ (by decide)
  intro base'
  -- Step 3: scalarmult k base' — by helper lemma
  exact curve25519_x25519_scalarmult_isOk k base'

/-- P-256 scalar multiplication does not panic. -/
theorem p256_scalar_mult_32_isOk (k p : Vector UInt8 32) :
    RustM.IsOk (Libcrux_specs.Fixed.p256_scalar_mult_32 k p) := by
  sorry

/-- P-256 base point multiplication does not panic. -/
theorem p256_base_mult_32_isOk (k : Vector UInt8 32) :
    RustM.IsOk (Libcrux_specs.Fixed.p256_base_mult_32 k) := by
  sorry

/-! ## Consequence: `getD` faithfulness

Once the `_isOk` theorems above are proved, these corollaries show
that `LibcruxSpecs.Specs` definitions are faithful (the zero-vector
fallback is unreachable). -/

/-- `LibcruxSpecs.sha256_32` equals the extracted result (no fallback). -/
theorem sha256_32_faithful (msg : Vector UInt8 32) :
    LibcruxSpecs.sha256_32 msg =
      (Libcrux_specs.Fixed.sha256_32 msg).getOk (sha256_32_isOk msg) :=
  (Libcrux_specs.Fixed.sha256_32 msg).getD_eq_getOk _ (sha256_32_isOk msg)

end LibcruxSpecs.PanicFree
