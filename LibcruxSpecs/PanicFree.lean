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

/-! ### SHA-256 family

Leaf-function helpers below mirror the AES helper pattern (`aes128_key_expand_isOk`,
`aes_encrypt_rounds_isOk`): they are kept as named TODOs so the wrapper-level
proofs are genuine compositions. -/

/-- Helper: the inner `Libcrux_specs.Sha256.sha256` always succeeds on any slice.
    (Proof TODO — requires reasoning through 4 nested `fold_range`s, byte-length
    arithmetic, and the `Sha256.compress` block function.) -/
theorem sha256_isOk (msg : Array UInt8) :
    (Libcrux_specs.Sha256.sha256 msg).isOk = true := by
  sorry  -- TODO: deep proof through 4 nested fold_range loops + compress

/-- SHA-256 on 32-byte input does not panic.
    Compositional: `unsize msg` then `Sha256.sha256`. -/
theorem sha256_32_isOk (msg : Vector UInt8 32) :
    RustM.IsOk (Libcrux_specs.Fixed.sha256_32 msg) := by
  unfold RustM.IsOk Libcrux_specs.Fixed.sha256_32
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · exact unsize_isOk msg
  intro slice
  exact sha256_isOk slice

/-- Helper: the inner `Libcrux_specs.Hmac.hmac_sha256` always succeeds.
    (Proof TODO — requires `sha256_isOk` plus reasoning through ~8 nested
    `fold_range`s and `Vec` capacity arithmetic.) -/
theorem hmac_sha256_isOk (key msg : Array UInt8) :
    (Libcrux_specs.Hmac.hmac_sha256 key msg).isOk = true := by
  sorry  -- TODO: deep proof; reduces to sha256_isOk + length arithmetic

/-- HMAC-SHA256 on 32-byte key and message does not panic.
    Compositional: two `unsize` calls then `Hmac.hmac_sha256`. -/
theorem hmac_sha256_32_isOk (key msg : Vector UInt8 32) :
    RustM.IsOk (Libcrux_specs.Fixed.hmac_sha256_32 key msg) := by
  unfold RustM.IsOk Libcrux_specs.Fixed.hmac_sha256_32
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · exact unsize_isOk key
  intro key_slice
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · exact unsize_isOk msg
  intro msg_slice
  exact hmac_sha256_isOk key_slice msg_slice

/-- Helper: the inner `Libcrux_specs.Hkdf.hkdf_extract` always succeeds.

    Compositional: the do-block desugars to `bind (is_empty salt) (fun b => if b
    then default_salt[RangeFull.mk]_? >>= hmac else hmac salt ikm)`. Both
    branches reduce to `hmac_sha256_isOk` after trivial `pure`-style steps;
    `is_empty` is unconditionally `IsOk`. -/
theorem hkdf_extract_isOk (salt ikm : Array UInt8) :
    (Libcrux_specs.Hkdf.hkdf_extract salt ikm).isOk = true := by
  unfold Libcrux_specs.Hkdf.hkdf_extract
  -- Step 1: `repeat 0 32` always succeeds.
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · exact LibcruxSpecs.PanicFree.repeat_isOk _ _ rfl
  intro default_salt
  -- Step 2: branch on `is_empty salt`.
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · rfl  -- `is_empty salt` reduces to `pure (... == 0)`, hence `IsOk`.
  intro b
  cases b
  · -- non-empty: `pure salt >>= hmac` reduces to `hmac salt ikm`.
    exact hmac_sha256_isOk salt ikm
  · -- empty: `default_salt[RangeFull.mk]_? >>= hmac` indexes the full vector
    -- (unconditional) then hmacs.
    apply LibcruxSpecs.PanicFree.bind_isOk_simple
    · rfl  -- `default_salt[RangeFull.mk]_? = pure default_salt.toArray`.
    intro arr
    exact hmac_sha256_isOk arr ikm

/-- HKDF-Extract on 32-byte salt and IKM does not panic.
    Compositional: two `unsize` calls then `Hkdf.hkdf_extract`. -/
theorem hkdf_extract_32_isOk (salt ikm : Vector UInt8 32) :
    RustM.IsOk (Libcrux_specs.Fixed.hkdf_extract_32 salt ikm) := by
  unfold RustM.IsOk Libcrux_specs.Fixed.hkdf_extract_32
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · exact unsize_isOk salt
  intro salt_slice
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · exact unsize_isOk ikm
  intro ikm_slice
  exact hkdf_extract_isOk salt_slice ikm_slice

/-- HKDF-Expand on 32-byte PRK and 32-byte info does not panic.

    **Proof status: TODO.** Closeable compositionally once two infrastructure
    pieces land:

    1. A *strengthened* `hkdf_expand_isOk` that additionally proves
       `okm.toArray.size = length.toNat` — the length precondition is enforced
       by the panicking assertion at the top of `hkdf_expand` (n ≤ 255).
    2. Either threading that size through `bind_isOk_dep`, OR a new
       `bind_isOk_dep` variant that captures `x = .ok v` in the second
       hypothesis (existing `bind_isOk_dep` does so, but using it for a
       four-level nested bind makes the proof script unwieldy).

    Structure (once those land):
    - `unsize info` succeeds (preserves length 32).
    - `hkdf_expand prk info 32` succeeds with `okm.toArray.size = 32`.
    - `repeat 0 32` succeeds.
    - The OKM-copy `fold_range 0..32` succeeds: at each `i : usize` with
      `i.toNat < 32`, both `okm[i]_?` (Vec index, in bounds by size = 32)
      and `update_at_usize result i` (Vector index, `i.toNat < 32`) succeed.
      The body discharge then uses `fold_range_usize_isOk`. -/
theorem hkdf_expand_32_isOk (prk info : Vector UInt8 32) :
    RustM.IsOk (Libcrux_specs.Fixed.hkdf_expand_32 prk info) := by
  sorry  -- TODO: needs strengthened `hkdf_expand_isOk_with_size` returning
         --       `okm.toArray.size = 32`, plus `fold_range_usize_isOk` for the
         --       OKM-copy loop body (the `fold_range_usize_isOk` keystone is
         --       now in `PanicFreeInfra.lean`).

/-- Helper: AES-128 key expansion always succeeds.

    Structural decomposition:
    * `repeat (repeat 0 16) 11` → an 11-element vector of zero-blocks (always OK).
    * `update_at round_keys 0 key` → in-bounds because 0 < 11.
    * **Outer while-loop** `round = 1..10`, body indexed by `round`:
      * `round_keys[round - 1]_?` — needs `(round-1) < 11`; the loop cond
        `round ≤ 10` and the body-entry condition give `round ∈ [1, 10]`
        so `round - 1 ∈ [0, 9] ⊂ [0, 11)`.
      * `repeat 0 16 : Vector u8 16` — always OK.
      * Build `rot` as a 4-element vector from `prev[12..16]` — all indices
        in `[12, 16) ⊂ [0, 16)`.
      * **Inner while-loop 1** `j = 0..4`, body:
        * `SBOX[(cast u8→usize) rot[j]]_?` — cast result ∈ [0, 256) by
          `cast_u8_lt_256`; SBOX has size 256.
        * If `j == 0`: `prev[j] ^^^ sbox ^^^ RCON[round-1]` — `RCON` has size 10
          and `round - 1 ∈ [0, 9]`.
        * Else: `prev[j] ^^^ sbox`.
        * `update_at rk j _` — `j < 4 < 16`.
      * **Inner while-loop 2** `j = 4..16`, body:
        * `rk[j - 4]_?` and `prev[j]_?` — both indices in `[0, 16)`.
        * `update_at rk j _` — `j < 16`.
      * `update_at round_keys round rk` — `round ∈ [1, 10] ⊂ [0, 11)`.
      * `round +? 1` — no overflow since `round ≤ 10`.

    Invariant for the outer loop: `round.toNat ≤ 11` (because the cond is
    `round ≤ 10`, so `round.toNat ≤ 10` upon entry, then `round + 1 ≤ 11`).
    Invariants for the inner loops: `j.toNat ≤ 4` and `j.toNat ≤ 16`.

    **Status:** the structural decomposition above is complete; the remaining
    obligation is mechanical bind-chain walking using the infrastructure now in
    `PanicFreeInfra.lean` (`while_loop'_isOk_inv`, `usize_add_one_isOk_of_lt`,
    `usize_sub_isOk`, `vector_getElem_usize_isOk`, `update_at_usize_isOk`,
    `bind_eq_of_isOk`, `cast_u8_lt_256`). Estimated additional LOC: 300-400. -/
theorem aes128_key_expand_isOk (key : Vector UInt8 16) :
    (Libcrux_specs.Aes.aes128_key_expand key).isOk = true := by
  unfold Libcrux_specs.Aes.aes128_key_expand
  -- Step 1: repeat (← repeat 0 16) 11
  apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
    (LibcruxSpecs.PanicFree.repeat_isOk (n := 16) (0 : UInt8) (16 : usize) rfl)
  intro zero_block
  apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
    (LibcruxSpecs.PanicFree.repeat_isOk (n := 11) zero_block (11 : usize) rfl)
  intro round_keys_init
  -- Step 2: update_at round_keys 0 key
  apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
    (LibcruxSpecs.PanicFree.update_at_usize_isOk round_keys_init 0 key (by decide))
  intro round_keys_with_key
  -- Step 3: while loop round = 1..10
  apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
  · refine LibcruxSpecs.PanicFree.while_loop'_isOk_inv
      (inv := fun p => 1 ≤ p._0.toNat ∧ p._0.toNat ≤ 11) _ _ _ _ _ ?_ ?_ ?_ ?_
    · rintro ⟨round, _⟩ _; rfl
    · -- Body IsOk
      rintro ⟨round, round_keys⟩ ⟨hround_lo, _hround_hi⟩ hcond
      simp only at hcond ⊢
      have hround_le10 : round.toNat ≤ 10 := by
        have := LibcruxSpecs.PanicFree.usize_le_of_machine_le hcond
        change round.toNat ≤ (10 : usize).toNat at this
        have h10 : (10 : usize).toNat = 10 := rfl
        rw [h10] at this; exact this
      -- round - 1
      have hround_lo' : 1 ≤ round.toNat := by simp only at hround_lo; exact hround_lo
      have hsub : (round -? (1 : usize)).isOk = true := by
        apply LibcruxSpecs.PanicFree.usize_sub_isOk
        show (1 : usize).toNat ≤ round.toNat
        have h1 : (1 : usize).toNat = 1 := rfl
        omega
      apply LibcruxSpecs.PanicFree.bind_isOk_dep _ _ hsub
      intro round_m1 hround_m1_eq
      have hround_m1_val : round_m1.toNat = round.toNat - 1 := by
        have hnov : ¬ BitVec.usubOverflow round.toBitVec (1 : usize).toBitVec := by
          simp [BitVec.usubOverflow]; omega
        have : (round -? (1 : usize)) = .ok (round - (1 : usize)) := by
          show (if BitVec.usubOverflow round.toBitVec (1 : usize).toBitVec
                then RustM.fail Error.integerOverflow
                else pure (round - (1 : usize))) = _
          rw [if_neg hnov]; rfl
        rw [this] at hround_m1_eq
        have heq : round_m1 = round - (1 : usize) := (RustM.ok.inj hround_m1_eq).symm
        rw [heq, USize64.toNat_sub_of_le']
        · have h1 : (1 : usize).toNat = 1 := rfl; rw [h1]
        · have h1 : (1 : usize).toNat = 1 := rfl; rw [h1]; exact hround_lo
      have hround_m1_lt11 : round_m1.toNat < 11 := by rw [hround_m1_val]; omega
      -- prev := round_keys[round - 1]_?
      apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
        (LibcruxSpecs.PanicFree.vector_getElem_usize_isOk round_keys round_m1 hround_m1_lt11)
      intro prev
      -- rk := repeat 0 16
      apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
        (LibcruxSpecs.PanicFree.repeat_isOk (n := 16) (0 : UInt8) (16 : usize) rfl)
      intro rk_init
      -- rot := #v[prev[13], prev[14], prev[15], prev[12]]
      apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
        (LibcruxSpecs.PanicFree.vector_getElem_usize_isOk prev (13 : usize) (by decide))
      intro v13
      apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
        (LibcruxSpecs.PanicFree.vector_getElem_usize_isOk prev (14 : usize) (by decide))
      intro v14
      apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
        (LibcruxSpecs.PanicFree.vector_getElem_usize_isOk prev (15 : usize) (by decide))
      intro v15
      apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
        (LibcruxSpecs.PanicFree.vector_getElem_usize_isOk prev (12 : usize) (by decide))
      intro v12
      -- Inner while_loop 1: j = 0..4.  Body: SBOX[cast rot[j]] then XOR + update_at;
      -- under invariant `j.toNat ≤ 4` and cond `j < 4`, each step in bounds.
      -- TODO: ~80 LOC of mechanical bind-chain walking, structurally identical to
      -- the `sub_bytes_isOk` body proof but with an if-then-else on `j == 0`.
      apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
      · sorry  -- TODO inner-loop-1: invariant j ≤ 4, body chain ~10 binds
      intro inner1_result
      -- Inner while_loop 2: j = 4..16.  Body: rk[j-4] XOR prev[j] then update_at.
      -- Invariant j.toNat ≤ 16; under cond j < 16, `j - 4 ≥ 0` and all indices < 16.
      apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
      · sorry  -- TODO inner-loop-2: invariant 4 ≤ j ≤ 16, body chain ~6 binds
      intro inner2_result
      -- update_at round_keys round rk
      apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
        (LibcruxSpecs.PanicFree.update_at_usize_isOk round_keys round.toNat inner2_result._1
          (by simpa using (by omega : round.toNat < 11)))
      intro new_round_keys
      -- round +? 1
      apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
        (LibcruxSpecs.PanicFree.usize_add_one_isOk_of_lt (N := 11) round
          (by omega) (by decide))
      intro round'
      rfl
    · -- Invariant preservation
      rintro ⟨round, round_keys⟩ ⟨round', round_keys'⟩ ⟨hround_lo, _⟩ hcond hbody
      simp only at hcond hbody
      have hround_le10 : round.toNat ≤ 10 := by
        have := LibcruxSpecs.PanicFree.usize_le_of_machine_le hcond
        change round.toNat ≤ (10 : usize).toNat at this
        have h10 : (10 : usize).toNat = 10 := rfl
        rw [h10] at this; exact this
      -- Walk body forward: the outer body has many bind steps (round-1, getElem prev,
      -- repeat 0 16, four prev getElems, inner-loop-1, inner-loop-2, update_at, round+1).
      -- The post-`round` value is set by the final `round +? 1` step.  TODO: ~50 LOC.
      refine ⟨?_, ?_⟩
      · sorry  -- TODO: round'.toNat ≥ 1 (from round.toNat ≥ 1 and round' = round + 1)
      · sorry  -- TODO: round'.toNat ≤ 11 (from round.toNat ≤ 10 and round' = round + 1)
    · -- Initial invariant
      refine ⟨?_, ?_⟩
      · show 1 ≤ (1 : usize).toNat; decide
      · show (1 : usize).toNat ≤ 11; decide
  intro ⟨_, _⟩
  rfl

/-- Helper: AES encryption rounds always succeed when given ≥ 11 round_keys.

    Compositional proof:
    * `add_round_key plaintext (← round_keys[0]_?)` — `0 < 11 ≤ round_keys.size`,
      then `add_round_key_isOk` (proved in `PanicFreeInfra.lean`).
    * **While-loop** `round = 1..10`, with invariant `round.toNat ≤ 10`:
      * `sub_bytes state` — by `sub_bytes_isOk`.
      * `shift_rows state` — by `shift_rows_isOk` (TODO).
      * `mix_columns state` — by `mix_columns_isOk` (TODO).
      * `round_keys[round]_?` — `round.toNat ≤ 9 < 11 ≤ round_keys.size`.
      * `add_round_key state rk` — by `add_round_key_isOk`.
      * `round +? 1` — no overflow (`round.toNat ≤ 9`).
    * Final `sub_bytes`, `shift_rows`, `add_round_key state (← round_keys[10]_?)`
      — `10 < 11 ≤ round_keys.size`.

    Pre-condition `11 ≤ round_keys.size` ensures all `round_keys[k]_?` for
    `k ∈ [0, 10]` succeed.

    Inherits `mix_columns_isOk` and `shift_rows_isOk` sorries from
    `PanicFreeInfra.lean`. -/
theorem aes_encrypt_rounds_isOk (pt : Vector UInt8 16)
    (round_keys : Array (Vector UInt8 16))
    (h : 11 ≤ round_keys.size) :
    (Libcrux_specs.Aes.aes_encrypt_rounds pt round_keys (10 : usize)).isOk = true := by
  unfold Libcrux_specs.Aes.aes_encrypt_rounds
  -- First add_round_key with round_keys[0]
  have hrk0 : (round_keys[(0 : usize)]_? : RustM (Vector UInt8 16)).isOk = true :=
    LibcruxSpecs.PanicFree.array_getElem_usize_isOk round_keys (0 : usize)
      (by show (0:usize).toNat < round_keys.size
          have : (0:usize).toNat = 0 := rfl; rw [this]; omega)
  apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _ hrk0
  intro rk0
  apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
    (LibcruxSpecs.PanicFree.add_round_key_isOk pt rk0)
  intro state0
  -- The while loop over rounds 1..10
  apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
  · refine LibcruxSpecs.PanicFree.while_loop'_isOk_inv
      (inv := fun p => p._0.toNat ≤ 10) _ _ _ _ _ ?_ ?_ ?_ ?_
    · rintro ⟨round, _⟩ _; rfl
    · -- Body IsOk
      rintro ⟨round, state⟩ _hinv hcond
      simp only at hcond ⊢
      have hround : round.toNat < 10 := by
        have := LibcruxSpecs.PanicFree.usize_lt_of_machine_lt hcond
        change round.toNat < (10 : usize).toNat at this
        have h10 : (10 : usize).toNat = 10 := rfl
        rw [h10] at this; exact this
      apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
        (LibcruxSpecs.PanicFree.sub_bytes_isOk state)
      intro s1
      apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
        (LibcruxSpecs.PanicFree.shift_rows_isOk s1)
      intro s2
      apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
        (LibcruxSpecs.PanicFree.mix_columns_isOk s2)
      intro s3
      apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
        (LibcruxSpecs.PanicFree.array_getElem_usize_isOk round_keys round
          (by show round.toNat < round_keys.size; omega))
      intro rk
      apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
        (LibcruxSpecs.PanicFree.add_round_key_isOk s3 rk)
      intro s4
      apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
        (LibcruxSpecs.PanicFree.usize_add_one_isOk_of_lt (N := 10) round hround (by decide))
      intro round'
      rfl
    · -- Invariant preservation
      rintro ⟨round, state⟩ ⟨round', state'⟩ _hinv hcond hbody
      simp only at hcond hbody
      have hround : round.toNat < 10 := by
        have := LibcruxSpecs.PanicFree.usize_lt_of_machine_lt hcond
        change round.toNat < (10 : usize).toNat at this
        have h10 : (10 : usize).toNat = 10 := rfl
        rw [h10] at this; exact this
      -- Walk forward to extract `round' = round + 1`.
      have hsb : (Libcrux_specs.Aes.sub_bytes state).isOk = true :=
        LibcruxSpecs.PanicFree.sub_bytes_isOk state
      obtain ⟨s1, _, hsb_rw⟩ := LibcruxSpecs.PanicFree.bind_eq_of_isOk _ (fun _ => _) hsb
      rw [hsb_rw] at hbody
      have hsr : (Libcrux_specs.Aes.shift_rows s1).isOk = true :=
        LibcruxSpecs.PanicFree.shift_rows_isOk s1
      obtain ⟨s2, _, hsr_rw⟩ := LibcruxSpecs.PanicFree.bind_eq_of_isOk _ (fun _ => _) hsr
      rw [hsr_rw] at hbody
      have hmc : (Libcrux_specs.Aes.mix_columns s2).isOk = true :=
        LibcruxSpecs.PanicFree.mix_columns_isOk s2
      obtain ⟨s3, _, hmc_rw⟩ := LibcruxSpecs.PanicFree.bind_eq_of_isOk _ (fun _ => _) hmc
      rw [hmc_rw] at hbody
      have hrk : (round_keys[round]_? : RustM (Vector UInt8 16)).isOk = true :=
        LibcruxSpecs.PanicFree.array_getElem_usize_isOk round_keys round (by
          show round.toNat < round_keys.size; omega)
      obtain ⟨rk, _, hrk_rw⟩ := LibcruxSpecs.PanicFree.bind_eq_of_isOk _ (fun _ => _) hrk
      rw [hrk_rw] at hbody
      have hark : (Libcrux_specs.Aes.add_round_key s3 rk).isOk = true :=
        LibcruxSpecs.PanicFree.add_round_key_isOk s3 rk
      obtain ⟨s4, _, hark_rw⟩ := LibcruxSpecs.PanicFree.bind_eq_of_isOk _ (fun _ => _) hark
      rw [hark_rw] at hbody
      have h_add1 : (round +? (1 : usize)).isOk = true :=
        LibcruxSpecs.PanicFree.usize_add_one_isOk_of_lt (N := 10) round hround (by decide)
      obtain ⟨round_new, hrn_eq, hrn_rw⟩ :=
        LibcruxSpecs.PanicFree.bind_eq_of_isOk _ (fun _ => _) h_add1
      rw [hrn_rw] at hbody
      have hpair : (Rust_primitives.Hax.Tuple2.mk round_new s4
                     : Rust_primitives.Hax.Tuple2 _ _) =
                   Rust_primitives.Hax.Tuple2.mk round' state' := RustM.ok.inj hbody
      have heq : round_new = round' := by injection hpair
      show round'.toNat ≤ 10
      rw [← heq]
      have : round_new.toNat = round.toNat + 1 :=
        LibcruxSpecs.PanicFree.usize_add_one_toNat (N := 10) round round_new hround
          (by decide) hrn_eq
      rw [this]; omega
    · -- Init
      show (1 : usize).toNat ≤ 10; decide
  -- After while-loop: final sub_bytes, shift_rows, add_round_key
  rintro ⟨_round_final, state_final⟩
  simp only
  apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
    (LibcruxSpecs.PanicFree.sub_bytes_isOk state_final)
  intro s1
  apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
    (LibcruxSpecs.PanicFree.shift_rows_isOk s1)
  intro s2
  apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
    (LibcruxSpecs.PanicFree.array_getElem_usize_isOk round_keys (10 : usize)
      (by show (10:usize).toNat < round_keys.size
          have : (10:usize).toNat = 10 := rfl; rw [this]; omega))
  intro rk
  apply LibcruxSpecs.PanicFree.bind_isOk_simple _ _
    (LibcruxSpecs.PanicFree.add_round_key_isOk s2 rk)
  intro _
  rfl

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
  -- hsl : pure round_keys.toArray = .ok slice, i.e. .ok round_keys.toArray = .ok slice
  injection hsl with hsl
  rw [← hsl]
  simp [Vector.size_toArray]

/-- AES-128-GCM seal on 32-byte buffers does not panic.

    **Proof status: TODO.** The wrapper itself is composable but blocks on a
    deep Layer-4 helper:
    `aes128_gcm_encrypt_isOk (key : Vector UInt8 16) (nonce : Vector UInt8 12)
      (aad pt : Array UInt8) : (Libcrux_specs.Aes_gcm.aes128_gcm_encrypt ...).isOk
      = true` — the GHASH / counter-mode encryption is panic-free in libcrux
    but the corresponding `_isOk` is not yet stated.

    Surrounding the call: three `fold_range_usize_isOk` calls (16-byte key
    extract, 12-byte nonce extract, ct/tag copy into the 32-byte result) and
    one branch on `len ct > 16` (both branches OK). Once
    `aes128_gcm_encrypt_isOk` lands the wrapper closes by a straightforward
    compositional chain. -/
theorem aes128_gcm_seal_32_isOk (key pt aad : Vector UInt8 32) :
    RustM.IsOk (Libcrux_specs.Fixed.aes128_gcm_seal_32 key pt aad) := by
  sorry  -- TODO: blocked on `Libcrux_specs.Aes_gcm.aes128_gcm_encrypt` isOk helper.

/-- AES-128-GCM open on 32-byte buffers does not panic.

    **Proof status: TODO.** Same Layer-4 blocker as `aes128_gcm_seal_32_isOk`:
    needs `aes128_gcm_decrypt_isOk` which proves
    `(Libcrux_specs.Aes_gcm.aes128_gcm_decrypt key nonce aad ct tag).isOk =
     true` and (for the Some branch) that the returned `pt` has a known length
    so the result-copy `fold_range` can be discharged.

    Surrounding the call: three `fold_range_usize_isOk` (key/nonce extract,
    tag copy) and a `match` on Option (the None branch is `repeat 0 32`, OK
    by `repeat_isOk`; the Some branch needs a length invariant on `pt`). -/
theorem aes128_gcm_open_32_isOk (key ct aad : Vector UInt8 32) :
    RustM.IsOk (Libcrux_specs.Fixed.aes128_gcm_open_32 key ct aad) := by
  sorry  -- TODO: blocked on `Libcrux_specs.Aes_gcm.aes128_gcm_decrypt` isOk helper
         --       (with length on the recovered plaintext).

/-! ### Curve25519 trivial sub-helpers

The two field-element constants are pure values and immediately satisfy the
`fe_fresh` (`limb < 2^52`) invariant. These are the only sub-helpers of
`curve25519_x25519_scalarmult_isOk` that close without machinery; the remaining
field-arithmetic helpers (`fe_add_isOk`, `fe_mul_isOk`, …) are deferred via
the TODO list in `curve25519_x25519_scalarmult_isOk`'s docstring. -/

/-- `fe_zero` is `pure (0,0,0,0,0)`, hence trivially `IsOk`. -/
theorem fe_zero_isOk (t : Rust_primitives.Hax.Tuple0) :
    (Libcrux_specs.Curve25519.fe_zero t).isOk = true := rfl

/-- `fe_one` is `pure (1,0,0,0,0)`, hence trivially `IsOk`. -/
theorem fe_one_isOk (t : Rust_primitives.Hax.Tuple0) :
    (Libcrux_specs.Curve25519.fe_one t).isOk = true := rfl

/-- The zero field element trivially satisfies the "fresh" limb invariant. -/
theorem fe_fresh_zero :
    LibcruxSpecs.PanicFree.fe_fresh
      (#v[(0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64)]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp <;> decide

/-- The one field element trivially satisfies the "fresh" limb invariant. -/
theorem fe_fresh_one :
    LibcruxSpecs.PanicFree.fe_fresh
      (#v[(1 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64)]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp <;> decide

/-- Helper: Curve25519 internal scalar mult always succeeds.

    **Proof status:** open. Requires limb-bound invariants threaded through the
    255-iteration Montgomery ladder. See `LibcruxSpecs.PanicFree.fe_fresh`
    (each of the five `u64` limbs `< 2^52`) and `LibcruxSpecs.PanicFree.fe_loose`
    (each limb `< 2^54`) for the canonical invariants — these are defined in
    `PanicFreeInfra.lean`'s "Curve25519 limb helpers" section.

    **Decomposition (each TODO is a sub-helper, in dependency order):**

    1. `fe_zero_isOk`, `fe_one_isOk` — pure constants; trivial (`rfl`).
    2. `cswap_isOk swap a b` — unconditional (body uses only `&&&?`, `^^^?`,
       `update_at_usize` with `i < 5` invariant). Uses `while_loop'_isOk_inv`
       with invariant `i.toNat ≤ 5`.
    3. `fe_carry_isOk a` — unconditional on the `Vector u64 5` (the input
       limbs can be arbitrarily large; carry chain folds them down). Each
       `+? carry` needs `MASK51 + carry < 2^64`, which holds because `carry`
       comes from `>>>? 51` of a `u64`, hence `< 2^13`.
    4. `fe_add_isOk a b`, `fe_sub_isOk a b` — preconditioned on `fe_fresh a`
       and `fe_fresh b`. Each limb-sum is `< 2^53`, fits in `u64`; then
       `fe_carry` produces `fe_fresh` output. (`fe_sub` adds a `≤ 2^52` bias
       per limb; sum still `< 2^53 + 2^52 < 2^54`.)
    5. `fe_mul_isOk a b` — preconditioned on `fe_loose a` and `fe_loose b`.
       Each `u128` schoolbook product `a_i * b_j ≤ (2^54)^2 = 2^108`; sum of
       five plus 19-scaled wraparound `< 2^113`, fits in `u128`. Final
       `fe_carry`-style chain produces `fe_fresh` output.
    6. `fe_sq_isOk a` — `fe_mul a a` with same precondition.
    7. `fe_mul_121666_isOk a` — same as `fe_mul`; `c = 121665 < 2^17`,
       `a_i * c < 2^71`, fits in `u128`.
    8. `fe_sq_n_isOk a n` — induction on `n`, uses `while_loop_fuel_isOk_inv`
       with invariant `fe_fresh r`.
    9. `fe_inv_isOk a` — composition of `fe_sq_n` and `fe_mul`; precondition
       `fe_fresh a` propagates through the addition chain.
    10. `fe_from_bytes_isOk b` — uncomplicated: bit shifts, masks; output is
        `fe_fresh` (each limb has MASK51 applied).
    11. `fe_to_bytes_isOk a` — preconditioned on `fe_fresh a`. Calls
        `fe_reduce` (also needs `fe_reduce_isOk`), then 4×8 `while_loop'`.

    **Top-level proof structure for `curve25519_x25519_scalarmult_isOk`:**

    * Clamp loop (32 iterations): invariant `i.toNat ≤ 32`. Uses leaf
      `vector_getElem_usize_isOk` + `update_at_usize_isOk` + `usize_add_isOk`.
    * Three explicit `update_at_usize` clamp steps: trivial bounds.
    * `fe_from_bytes u`: gives `fe_fresh x_1`.
    * `fe_one/zero`: give `fe_fresh x_2 z_2 z_3`. `x_3 := x_1`.
    * **Main ladder loop (255 iterations):** invariant
      `pos.toInt ≥ -1 ∧ fe_fresh x_2 ∧ fe_fresh z_2 ∧ fe_fresh x_3 ∧ fe_fresh z_3`.
      Body: bit-extract (always OK), two `cswap` (OK), `fe_add`/`fe_sub`
      (preserve `fe_fresh`), `fe_sq`/`fe_mul`/`fe_mul_121666` (preserve
      `fe_fresh`), `pos -? 1` (`pos ≥ 0` from cond).
    * Final two `cswap` and `fe_inv z_2`, `fe_mul x_2 ...`, `fe_to_bytes`.

    **Estimated size:** ~600 LOC across the 11 helpers + ladder proof.
    **Blocking:** none — all required infrastructure (`while_loop_fuel_isOk_inv`,
    `usize_add_isOk`, `vector_getElem_*_isOk`, `update_at_usize_isOk`,
    `usize_sub_isOk`) is now in `PanicFreeInfra.lean`. -/
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

/-! ### P-256 family

The two wrapper theorems below follow the compositional AES pattern: each is
a real `bind_isOk_simple` chain through the leaf helpers
`p256_fp_*_isOk`, `p256_scalar_mult_isOk`, `p256_to_affine_isOk`, and
`fp_sqrt_p256_isOk` declared in this section.  The leaf helpers themselves
remain `sorry`-ed — each one needs limb-range and `usize`-overflow
invariants through its inner `while_loop'`/`fold_range`, analogous to the
Curve25519 `fe_*_isOk` plan in `PanicFreeInfra.lean`.  See per-leaf
docstrings for the specific invariant each one requires. -/

/-- Field addition mod p always succeeds.  (Proof TODO — `add256` runs a
    `while_loop'` decrementing `i` from `4`; needs invariant `0 ≤ i ≤ 4`
    so `i -? 1`, the limb index `r[i]_?`, and the final `cmp256`/sub256
    branch all succeed.) -/
theorem p256_fp_add_isOk (a b : Vector UInt64 4) :
    (Libcrux_specs.P256.fp_add a b).isOk = true := by
  sorry  -- TODO: while_loop'_isOk_inv with i ≤ 4 ; reuses add256/sub256/cmp256 isOk

/-- Field subtraction mod p always succeeds.  (Proof TODO — same shape as
    `p256_fp_add_isOk`; the `sub256` path uses `wrapping_sub` so no
    overflow there.) -/
theorem p256_fp_sub_isOk (a b : Vector UInt64 4) :
    (Libcrux_specs.P256.fp_sub a b).isOk = true := by
  sorry  -- TODO: while_loop'_isOk_inv with i ≤ 4 ; reuses sub256/add256 isOk

/-- Field multiplication mod p always succeeds.  (Proof TODO — schoolbook
    `mul256_full` is a 4×4 nested `while_loop'`; outer invariant `i ≤ 4`,
    inner invariant `j ≤ 4 ∧ i ≤ 4`; the cross-product `prod := a[3-i] *
    b[3-j] + r[i+j] + carry` is panic-free because `(2^64-1)^2 + 2*(2^64-1) <
    2^128`. Final `reduce_mod_p` is pure (`Nat` arithmetic). -/
theorem p256_fp_mul_isOk (a b : Vector UInt64 4) :
    (Libcrux_specs.P256.fp_mul a b).isOk = true := by
  sorry  -- TODO: 4×4 nested while_loop'_isOk_inv ; reduce_mod_p is pure

/-- Field squaring always succeeds.  Reduces to `p256_fp_mul_isOk`. -/
theorem p256_fp_sq_isOk (a : Vector UInt64 4) :
    (Libcrux_specs.P256.fp_sq a).isOk = true := by
  unfold Libcrux_specs.P256.fp_sq
  exact p256_fp_mul_isOk a a

/-- Field inversion (Fermat's little theorem) always succeeds.  (Proof TODO —
    the inversion loop runs `while_loop'` with `bit_pos : i32` decrementing
    from `255`; the invariant is `-1 ≤ bit_pos.toInt ≤ 255` so that
    `bit_pos /? 64` is nonzero-divisor, `bit_pos %? 64` succeeds, the cast
    `bit_pos / 64 : usize` is `≤ 3`, and `3 -? word` doesn't underflow.) -/
theorem p256_fp_inv_isOk (a : Vector UInt64 4) :
    (Libcrux_specs.P256.fp_inv a).isOk = true := by
  sorry  -- TODO: 256-iter while_loop'_isOk_inv with -1 ≤ bit_pos ≤ 255 invariant

/-- Encode a field element to 32 bytes always succeeds.  (Proof TODO — nested
    4×8 `while_loop'`; outer invariant `i ≤ 4` (so `i *? 8 ≤ 32`), inner
    invariant `j ≤ 8 ∧ i < 4 ∧ i*8+j ≤ 32` (so `out[i*8+j]_?` is in bounds). -/
theorem p256_fp_to_bytes_isOk (a : Vector UInt64 4) :
    (Libcrux_specs.P256.fp_to_bytes a).isOk = true := by
  sorry  -- TODO: nested 4×8 while_loop'_isOk_inv with i*8+j < 32 invariant

/-- Decode a field element from 32 bytes always succeeds.  (Proof TODO —
    same shape as `p256_fp_to_bytes_isOk`. -/
theorem p256_fp_from_bytes_isOk (b : Vector UInt8 32) :
    (Libcrux_specs.P256.fp_from_bytes b).isOk = true := by
  sorry  -- TODO: nested 4×8 while_loop'_isOk_inv (mirror of fp_to_bytes)

/-- Scalar multiplication `k * P` always succeeds.
    (Proof TODO — 256-iter `while_loop'` whose body does `point_double`,
    `byte_idx := i / 8`, `bit_idx := 7 - i % 8`, `k[byte_idx]_?`, then
    conditionally `point_add`.  Invariant: `i.toNat ≤ 256` so that
    `i +? 1` doesn't overflow, `i / 8 ≤ 32` so `k[i/8]_?` is in bounds
    when `i < 256`, and `i % 8 ≤ 7` so `7 -? (i%8)` doesn't underflow.
    Body reduces to `p256_point_double_isOk` and `p256_point_add_isOk`. -/
theorem p256_scalar_mult_isOk (k : Vector UInt8 32) (p : Libcrux_specs.P256.P256Point) :
    (Libcrux_specs.P256.scalar_mult k p).isOk = true := by
  sorry  -- TODO: 256-iter while_loop'_isOk_inv ; body needs point_double/add isOk

/-- Base-point multiplication `k * G` always succeeds.  Reduces to
    `p256_scalar_mult_isOk` after the trivial `base_point` step (which is
    `pure (P256Point.mk ...)`). -/
theorem p256_base_mult_isOk (k : Vector UInt8 32) :
    (Libcrux_specs.P256.base_mult k).isOk = true := by
  unfold Libcrux_specs.P256.base_mult
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · -- `base_point ()` is a `pure` literal, hence always IsOk.
    rfl
  intro g
  exact p256_scalar_mult_isOk k g

/-- Jacobian → affine conversion always succeeds.  Composes `fp_inv`,
    `fp_sq`, and three `fp_mul`s. -/
theorem p256_to_affine_isOk (p : Libcrux_specs.P256.P256Point) :
    (Libcrux_specs.Fixed.p256_to_affine p).isOk = true := by
  unfold Libcrux_specs.Fixed.p256_to_affine
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · exact p256_fp_inv_isOk _
  intro z_inv
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · exact p256_fp_sq_isOk _
  intro z_inv2
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · exact p256_fp_mul_isOk _ _
  intro z_inv3
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · exact p256_fp_mul_isOk _ _
  intro x'
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · exact p256_fp_mul_isOk _ _
  intro y'
  rfl

/-- The 255-iteration sqrt loop always succeeds.
    (Proof TODO — once a `fold_range_isOk_const` (constant-body fold_range
    preservation) lemma lands in `PanicFreeInfra.lean`, this reduces to
    `p256_fp_sq_isOk` and `p256_fp_mul_isOk` in the body. -/
theorem fp_sqrt_p256_isOk (a : Vector UInt64 4) :
    (Libcrux_specs.Fixed.fp_sqrt_p256 a).isOk = true := by
  sorry  -- TODO: needs fold_range_isOk_const ; body is fp_sq ∘ fp_mul, both isOk

/-- P-256 base point multiplication does not panic.
    Compositional: `base_mult k → p256_to_affine → fp_to_bytes ∘ .x`. -/
theorem p256_base_mult_32_isOk (k : Vector UInt8 32) :
    RustM.IsOk (Libcrux_specs.Fixed.p256_base_mult_32 k) := by
  unfold RustM.IsOk Libcrux_specs.Fixed.p256_base_mult_32
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · exact p256_base_mult_isOk k
  intro result
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · exact p256_to_affine_isOk result
  intro affine
  exact p256_fp_to_bytes_isOk _

/-- P-256 scalar multiplication does not panic.
    Compositional: `fp_from_bytes`, then an `fp_sq`/`fp_mul` chain to
    recompute the y-coordinate, `fp_sqrt_p256`, `scalar_mult`,
    `p256_to_affine`, and finally `fp_to_bytes`. -/
theorem p256_scalar_mult_32_isOk (k p : Vector UInt8 32) :
    RustM.IsOk (Libcrux_specs.Fixed.p256_scalar_mult_32 k p) := by
  unfold RustM.IsOk Libcrux_specs.Fixed.p256_scalar_mult_32
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · exact p256_fp_from_bytes_isOk p
  intro px_fe
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · exact p256_fp_sq_isOk px_fe
  intro x2
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · exact p256_fp_mul_isOk x2 px_fe
  intro x3
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · exact p256_fp_mul_isOk px_fe _
  intro three_x
  -- The `let rhs ← fp_add (← fp_sub x3 three_x) P256_B` desugars to two binds.
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · exact p256_fp_sub_isOk x3 three_x
  intro diff
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · exact p256_fp_add_isOk diff _
  intro rhs
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · exact fp_sqrt_p256_isOk rhs
  intro py_fe
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · exact p256_scalar_mult_isOk k _
  intro result
  apply LibcruxSpecs.PanicFree.bind_isOk_simple
  · exact p256_to_affine_isOk result
  intro affine
  exact p256_fp_to_bytes_isOk _

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
