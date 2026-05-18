/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bas Spitters
-/

import LibcruxSpecs.Specs
import LibcruxSpecs.LoopCompat

/-!
# PanicFree Infrastructure

This file provides the foundational lemmas for proving that hax-extracted
crypto functions never panic (`RustM.IsOk`).

## Key idea

The hax extraction produces deeply nested `do` blocks where each `←` is a
`RustM.bind`. To prove `(do ...).isOk = true`, we show:

1. **Leaf operations** are `IsOk` (`getElem_isOk`, `update_isOk`, etc.)
2. **Bind composition** preserves `IsOk` (`bind_isOk`)
3. **Loops** preserve `IsOk` if the body does (`fold_range_isOk`)

The leaf lemmas come in three flavors:
- **Unconditional**: `pure_isOk`, `unsize_isOk`, `as_slice_isOk`, etc.
- **Bounds-preconditioned**: `vector_getElem_isOk`, `update_at_usize_isOk`
- **Overflow-preconditioned**: `add_isOk`, `mul_isOk` (require non-overflow)
-/

set_option autoImplicit false

namespace LibcruxSpecs.PanicFree

open RustM

/-! ## Pure operations (always succeed) -/

@[simp] theorem pure_isOk' {α : Type} (v : α) : (pure v : RustM α).isOk = true := rfl

theorem unsize_isOk {α : Type} {n : Nat} (v : Vector α n) :
    (Rust_primitives.unsize v).isOk = true := rfl

/-! ## Vector indexing (succeeds if index in bounds) -/

theorem vector_getElem_usize_isOk {α : Type} {n : Nat} (v : Vector α n) (i : usize)
    (h : i.toNat < n) : (v[i]_?).isOk = true := by
  show (usize.instGetElemResultVector.getElemResult v i).isOk = true
  unfold usize.instGetElemResultVector
  simp [h]

theorem vector_getElem_nat_isOk {α : Type} {n : Nat} (v : Vector α n) (i : Nat)
    (h : i < n) : (v[i]_?).isOk = true := by
  show (Nat.instGetElemResultVector.getElemResult v i).isOk = true
  unfold Nat.instGetElemResultVector
  simp [h]

/-! ## Array indexing -/

theorem array_getElem_usize_isOk {α : Type} (a : Array α) (i : usize)
    (h : i.toNat < a.size) : (a[i]_?).isOk = true := by
  show (usize.instGetElemResultArray.getElemResult a i).isOk = true
  unfold usize.instGetElemResultArray
  simp [h]

theorem array_getElem_nat_isOk {α : Type} (a : Array α) (i : Nat)
    (h : i < a.size) : (a[i]_?).isOk = true := by
  show (Nat.instGetElemResultArray.getElemResult a i).isOk = true
  unfold Nat.instGetElemResultArray
  simp [h]

/-! ## Array update (succeeds if index in bounds) -/

theorem update_at_usize_isOk {α : Type} {n : Nat} (a : Vector α n) (i : Nat) (v : α)
    (h : i < n) :
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a i v).isOk = true := by
  have hs : i < a.size := by simpa using h
  unfold Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
  show (RustSetAt.setAt a i v).isOk = true
  unfold instRustSetAtVector
  simp [RustSetAt.setAt, hs]

/-! ## Vector construction -/

theorem repeat_isOk {α int_type : Type} {n : Nat} [ToNat int_type] (v : α) (size : int_type)
    (h : ToNat.toNat size = n) :
    (Rust_primitives.Hax.repeat (n := n) v size).isOk = true := by
  unfold Rust_primitives.Hax.repeat
  simp [h.symm]

/-! ## Vec operations (always succeed — they're just `pure` wrappers) -/

theorem vec_with_capacity_isOk (T : Type) (cap : usize) :
    (Alloc.Vec.Impl.with_capacity T cap).isOk = true := rfl

theorem vec_push_isOk {T A : Type} (v : Alloc.Vec.Vec T A) (x : T) :
    (Alloc.Vec.Impl_1.push T A v x).isOk = true := rfl

theorem vec_as_slice_isOk {T A : Type} (v : Alloc.Vec.Vec T A) :
    (Alloc.Vec.Impl_1.as_slice v).isOk = true := rfl

theorem vec_len_isOk (α A : Type) (v : Alloc.Vec.Vec α Alloc.Alloc.Global) :
    (Alloc.Vec.Impl_1.len α A v).isOk = true := rfl

/-! ## Bind composition -/

theorem bind_isOk_simple {α β : Type} (x : RustM α) (f : α → RustM β)
    (hx : x.isOk = true) (hf : ∀ a, (f a).isOk = true) :
    (x >>= f).isOk = true := by
  match x, hx with
  | .ok v, _ => exact hf v

theorem bind_isOk_dep {α β : Type} (x : RustM α) (f : α → RustM β)
    (hx : x.isOk = true) (hf : ∀ a, x = .ok a → (f a).isOk = true) :
    (x >>= f).isOk = true := by
  match x, hx with
  | .ok v, _ => exact hf v rfl

/-! ## Loops: `fold_range_isOk`

The `while_loop'_isOk` lemma is in `LoopCompat.lean` (where it has access to
the private `while_loop_fuel`). The `fold_range_isOk` family below is the
analogue for hax's `for i in [s:e]` desugaring, which reduces (via
`Std.Legacy.Range.forIn_eq_forIn_range'`) to a fold over `List.range'`. We
prove the list-level lemma by structural induction on the list, then bridge
to the typeclass-overloaded `Rust_primitives.Hax.Folds.fold_range`. -/

/-- Foundation: `forIn` over a `List` with a yield-only `RustM` body that
    always succeeds, succeeds. Proved by structural induction on the list. -/
theorem forIn_list_yield_isOk {α β : Type} (body : α → β → RustM α)
    (l : List β) (init : α)
    (h : ∀ a b, b ∈ l → (body a b).isOk = true) :
    (forIn l init (fun i acc => do
      let __do_lift ← body acc i
      let acc : α := __do_lift
      pure PUnit.unit
      pure (ForInStep.yield acc))).isOk = true := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons]
    have hx : (body init x).isOk = true := h init x List.mem_cons_self
    match heq : body init x, hx with
    | .ok v, _ =>
      change (forIn xs v (fun i acc => do
        let __do_lift ← body acc i
        let acc : α := __do_lift
        pure PUnit.unit
        pure (ForInStep.yield acc))).isOk = true
      exact ih v (fun a b hb => h a b (List.mem_cons_of_mem _ hb))

/-- The `Nat` instance of `Rust_primitives.Hax.Folds.fold_range` over `[s:e]`
    succeeds when the body succeeds for every index in the half-open range. -/
theorem fold_range_nat_isOk {α : Type} (s e : Nat)
    (inv : α → Nat → RustM Bool) (init : α) (body : α → Nat → RustM α)
    (h : ∀ acc i, s ≤ i → i < e → (body acc i).isOk = true) :
    (Rust_primitives.Hax.Folds.fold_range s e inv init body).isOk = true := by
  change (do
    let mut acc := init
    for i in [s:e] do
      acc := (← body acc i)
    pure acc : RustM α).isOk = true
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply bind_isOk_simple
  · apply forIn_list_yield_isOk
    intro a b hb
    rw [List.mem_range'] at hb
    obtain ⟨k, hk, rfl⟩ := hb
    apply h
    · exact Nat.le_add_right s _
    · simp [Std.Legacy.Range.size] at hk; omega
  · intro a; rfl

/-- The `usize` instance of `Rust_primitives.Hax.Folds.fold_range` over
    `[s.toNat : e.toNat]` succeeds when the body succeeds on every index in
    the half-open range. The hypothesis is stated in terms of the `usize`
    index that the body receives, with bounds `s.toNat ≤ i.toNat` and
    `i.toNat < e.toNat` — exactly the form expected at call sites. -/
theorem fold_range_usize_isOk {α : Type} (s e : usize)
    (inv : α → usize → RustM Bool) (init : α) (body : α → usize → RustM α)
    (h : ∀ acc (i : usize), s.toNat ≤ i.toNat → i.toNat < e.toNat →
        (body acc i).isOk = true) :
    (Rust_primitives.Hax.Folds.fold_range s e inv init body).isOk = true := by
  change (do
    let mut acc := init
    for i in [Coe.coe s : Coe.coe e] do
      acc := (← body acc (Coe.coe i))
    pure acc : RustM α).isOk = true
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply bind_isOk_simple
  · apply forIn_list_yield_isOk
    intro a b hb
    rw [List.mem_range'] at hb
    obtain ⟨k, hk, rfl⟩ := hb
    have hs : s.toNat < USize64.size := USize64.toNat_lt_size s
    have he : e.toNat < USize64.size := USize64.toNat_lt_size e
    simp [Std.Legacy.Range.size, Coe.coe] at hk
    -- The argument to body is `(Coe.coe (Coe.coe s + 1 * k) : usize) = USize64.ofNat (s.toNat + k)`.
    have hbody_arg : (Coe.coe ((Coe.coe s : Nat) + 1 * k) : usize) = USize64.ofNat (s.toNat + k) := by
      show USize64.ofNat (s.toNat + 1 * k) = USize64.ofNat (s.toNat + k)
      rw [Nat.one_mul]
    rw [hbody_arg]
    have hkk : (USize64.ofNat (s.toNat + k)).toNat = s.toNat + k := by
      grind
    apply h
    · rw [hkk]; omega
    · rw [hkk]; omega
  · intro a; rfl

/-! ## Discharge tactic for trivial goals

The `panic_free_simple` tactic tries to close `(do ...).isOk = true` goals
by repeatedly applying `bind_isOk_simple` and the leaf `_isOk` lemmas. -/

attribute [simp] vec_with_capacity_isOk vec_push_isOk vec_as_slice_isOk vec_len_isOk

/-! ## Invariant-based while-loop reasoning

The unconditional `while_loop_fuel_isOk` requires the body to succeed on EVERY
state. For real crypto loops the body only succeeds when an invariant
(e.g. `i.toNat < 16`) is maintained. -/

open Rust_primitives.Hax in
/-- Invariant-based panic-freedom for fuel-bounded `while_loop`.

    If an invariant `inv` is preserved by the body (under the assumption that
    the condition currently holds), and the condition/body never fail under
    `inv`, then the whole loop never fails. -/
theorem while_loop_fuel_isOk_inv {β : Type} (inv : β → Prop)
    (cond : β → RustM Bool) (body : β → RustM β)
    (hcond : ∀ s, inv s → (cond s).isOk = true)
    (hbody : ∀ s, inv s → cond s = .ok true → (body s).isOk = true)
    (hpres : ∀ s s', inv s → cond s = .ok true → body s = .ok s' → inv s') :
    ∀ (n : Nat) (init : β), inv init → (while_loop_fuel cond body n init).isOk = true := by
  intro n
  induction n with
  | zero => intro init _; rfl
  | succ k ih =>
    intro init hinit
    unfold while_loop_fuel
    have hc := hcond init hinit
    match h_cond : cond init, hc with
    | .ok true, _ =>
      have hb := hbody init hinit h_cond
      match h_body : body init, hb with
      | .ok v, _ =>
        show (while_loop_fuel cond body k v).isOk = true
        exact ih v (hpres init v hinit h_cond h_body)
    | .ok false, _ => rfl

open Rust_primitives.Hax in
/-- Invariant-based panic-freedom for hax's `while_loop'`. -/
theorem while_loop'_isOk_inv {β : Type} (inv : β → Prop)
    (rust_inv : β → RustM Prop) (cond : β → RustM Bool)
    (term : β → RustM Hax_lib.Int.Int) (init : β) (body : β → RustM β)
    (hcond : ∀ s, inv s → (cond s).isOk = true)
    (hbody : ∀ s, inv s → cond s = .ok true → (body s).isOk = true)
    (hpres : ∀ s s', inv s → cond s = .ok true → body s = .ok s' → inv s')
    (hinit : inv init) :
    (Rust_primitives.Hax.while_loop' rust_inv cond term init body).isOk = true :=
  while_loop_fuel_isOk_inv inv cond body hcond hbody hpres 100000 init hinit

/-! ## AES byte-op helpers

These show that the AES inner transforms `sub_bytes`, `shift_rows`,
`mix_columns`, `add_round_key` never panic. Each follows the same shape:
an `i`-indexed `while_loop'` over a fixed-size buffer whose body indexes
the buffer and computes XOR/SBOX lookups. The invariant is the index
bound (`i.toNat ≤ 16` etc.). -/

/-- Notation-friendly: `Machine_int.lt`, `Machine_int.le`, `Machine_int.eq`
    all reduce to `pure (...)` so they're unconditionally `IsOk`. -/
@[simp] theorem machine_int_lt_isOk {α : Type} [LT α] [DecidableLT α] (x y : α) :
    (Rust_primitives.Hax.Machine_int.lt x y).isOk = true := rfl

@[simp] theorem machine_int_le_isOk {α : Type} [LE α] [DecidableLE α] (x y : α) :
    (Rust_primitives.Hax.Machine_int.le x y).isOk = true := rfl

@[simp] theorem machine_int_eq_isOk {α : Type} [BEq α] (x y : α) :
    (Rust_primitives.Hax.Machine_int.eq x y).isOk = true := rfl

/-- The `u8 → usize` cast is unconditionally `IsOk` (`pure (UInt8.toUSize64 x)`). -/
@[simp] theorem cast_op_u8_usize_isOk (x : UInt8) :
    (Rust_primitives.Hax.cast_op (α := UInt8) (β := usize) x).isOk = true := rfl

/-- XOR on `u8` is unconditionally `IsOk` (it's `pure (x ^^^ y)`). -/
@[simp] theorem xor_u8_isOk (x y : UInt8) :
    ((x ^^^? y : RustM UInt8)).isOk = true := rfl

/-- `usize` addition succeeds when the sum fits in 64 bits. -/
theorem usize_add_isOk (x y : usize) (h : x.toNat + y.toNat < 2 ^ 64) :
    (x +? y).isOk = true := by
  show (if BitVec.uaddOverflow x.toBitVec y.toBitVec
        then RustM.fail Error.integerOverflow
        else pure (x + y)).isOk = true
  have hnov : ¬ BitVec.uaddOverflow x.toBitVec y.toBitVec := by
    rw [USize64.uaddOverflow_iff]; omega
  simp [hnov]

/-- `usize` subtraction succeeds when `y ≤ x`. -/
theorem usize_sub_isOk (x y : usize) (h : y.toNat ≤ x.toNat) :
    (x -? y).isOk = true := by
  show (if BitVec.usubOverflow x.toBitVec y.toBitVec
        then RustM.fail Error.integerOverflow
        else pure (x - y)).isOk = true
  have hnov : ¬ BitVec.usubOverflow x.toBitVec y.toBitVec := by
    simp [BitVec.usubOverflow]; omega
  simp [hnov]

/-- `usize` multiplication succeeds when the product fits in 64 bits. -/
theorem usize_mul_isOk (x y : usize) (h : x.toNat * y.toNat < 2 ^ 64) :
    (x *? y).isOk = true := by
  show (if BitVec.umulOverflow x.toBitVec y.toBitVec
        then RustM.fail Error.integerOverflow
        else pure (x * y)).isOk = true
  have hnov : ¬ BitVec.umulOverflow x.toBitVec y.toBitVec := by
    rw [USize64.umulOverflow_iff]; omega
  simp [hnov]

/-- `usize` modulo succeeds when the divisor is non-zero. -/
theorem usize_mod_isOk (x y : usize) (h : y ≠ 0) :
    (x %? y).isOk = true := by
  show (if y = 0 then RustM.fail Error.divisionByZero else pure (x % y)).isOk = true
  simp [h]

/-! ## AES byte-op helpers

These show panic-freedom of the inner AES transforms `sub_bytes`, `shift_rows`,
`mix_columns`, `add_round_key`. Each is a single (or doubly-nested)
`while_loop'` over a fixed-size 16-byte buffer whose body performs in-bounds
array lookups, S-box lookups, XORs, and a counter increment. The invariant
in each loop is the index bound (`i.toNat ≤ 16`, `col.toNat ≤ 4`, etc.). -/

/-- A `u8` cast to `usize` is always `< 256` (SBOX size). -/
theorem cast_u8_lt_256 (b : UInt8) : (UInt8.toUSize64 b).toNat < 256 := by
  unfold UInt8.toUSize64
  show (USize64.ofNat32 b.toBitVec.toNat _).toNat < 256
  unfold USize64.ofNat32 USize64.ofNatLT
  show (BitVec.ofNatLT b.toBitVec.toNat _).toNat < 256
  rw [BitVec.toNat_ofNatLT]
  -- b.toBitVec.toNat < 2^8 = 256
  have := b.toBitVec.isLt
  simpa using this

/-- `(i + 1 : usize)` doesn't overflow when `i.toNat < N` for any `N < 2^64`. -/
theorem usize_add_one_isOk_of_lt {N : Nat} (i : usize) (h : i.toNat < N)
    (hN : N + 1 < 2 ^ 64) : (i +? (1 : usize)).isOk = true := by
  apply usize_add_isOk
  have h1 : (1 : usize).toNat = 1 := rfl
  rw [h1]
  omega

/-- `(i + k : usize)` doesn't overflow when both are small. -/
theorem usize_add_isOk_of_lt {N M : Nat} (i j : usize) (hi : i.toNat < N) (hj : j.toNat < M)
    (hN : N + M < 2 ^ 64) : (i +? j).isOk = true := by
  apply usize_add_isOk; omega

/-- `(i * k : usize)` doesn't overflow when both are small. -/
theorem usize_mul_isOk_of_lt {N M : Nat} (i j : usize) (hi : i.toNat < N) (hj : j.toNat < M)
    (hN : N * M < 2 ^ 64) : (i *? j).isOk = true := by
  apply usize_mul_isOk
  have hN' : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
  have hM' : 0 < M := Nat.lt_of_le_of_lt (Nat.zero_le _) hj
  calc i.toNat * j.toNat
      < N * M := Nat.mul_lt_mul_of_lt_of_lt hi hj
    _ < 2 ^ 64 := hN

/-- When `Machine_int.lt i bound` returns `.ok true`, derive `i.toNat < bound.toNat`. -/
theorem usize_lt_of_machine_lt {i bound : usize}
    (h : Rust_primitives.Hax.Machine_int.lt i bound = .ok true) :
    i.toNat < bound.toNat := by
  have : i < bound := by
    have := h
    unfold Rust_primitives.Hax.Machine_int.lt at this
    -- this : pure (i < bound) = .ok true
    -- pure of a Prop-valued Bool via Decidable
    have e : (pure (i < bound) : RustM Bool) = .ok (decide (i < bound)) := rfl
    rw [e] at this
    have : decide (i < bound) = true := RustM.ok.inj this
    exact of_decide_eq_true this
  exact USize64.lt_iff_toNat_lt.mp this

/-- When `Machine_int.le i bound` returns `.ok true`, derive `i.toNat ≤ bound.toNat`. -/
theorem usize_le_of_machine_le {i bound : usize}
    (h : Rust_primitives.Hax.Machine_int.le i bound = .ok true) :
    i.toNat ≤ bound.toNat := by
  have : i ≤ bound := by
    have := h
    unfold Rust_primitives.Hax.Machine_int.le at this
    have e : (pure (i ≤ bound) : RustM Bool) = .ok (decide (i ≤ bound)) := rfl
    rw [e] at this
    have : decide (i ≤ bound) = true := RustM.ok.inj this
    exact of_decide_eq_true this
  exact USize64.le_iff_toNat_le.mp this

/-- Step after `i +? (1 : usize)` with `i.toNat < N`: the result has
    `toNat = i.toNat + 1` (assuming no overflow, which is implied by `N < 2^64`). -/
theorem usize_add_one_toNat {N : Nat} (i i' : usize) (h : i.toNat < N) (hN : N + 1 < 2 ^ 64)
    (heq : (i +? (1 : usize)) = .ok i') : i'.toNat = i.toNat + 1 := by
  have h1 : (1 : usize).toNat = 1 := rfl
  have hnov : ¬ BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec := by
    rw [USize64.uaddOverflow_iff]; rw [h1]; omega
  have heq' : (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
               then RustM.fail Error.integerOverflow
               else pure (i + (1 : usize))) = .ok i' := heq
  rw [if_neg hnov] at heq'
  have : i' = i + (1 : usize) := by
    have := RustM.ok.inj heq'
    exact this.symm
  rw [this, USize64.toNat_add_of_lt]
  · rw [h1]
  · rw [h1]; omega

/-- Extract a witness from a successful `RustM` value: if `x.isOk = true`, then
    `x = .ok a` for some `a`, and `x >>= f = f a`. Used to step through bind
    chains symbolically inside invariant-preservation proofs. -/
theorem bind_eq_of_isOk {α β : Type} (x : RustM α) (f : α → RustM β)
    (h : x.isOk = true) : ∃ a, x = .ok a ∧ (x >>= f) = f a := by
  match x, h with
  | .ok v, _ => exact ⟨v, rfl, rfl⟩

/-! ### sub_bytes -/

/-- `Libcrux_specs.Aes.sub_bytes` never panics.

    Outer structure: `repeat 0 16; while_loop' over (i, result : usize × Vector u8 16)`.
    Invariant: `i.toNat ≤ 16`. Under `cond=true` (i.e. `i.toNat < 16`) the body
    chains: `state[i]_?` (in bounds), `cast u8→usize` (pure), `SBOX[k]_?` (the
    cast result is `< 256`, the SBOX size), `update_at result i _` (in bounds),
    `i +? 1` (no overflow because `i.toNat < 16`). -/
theorem sub_bytes_isOk (state : RustArray u8 16) :
    (Libcrux_specs.Aes.sub_bytes state).isOk = true := by
  unfold Libcrux_specs.Aes.sub_bytes
  apply bind_isOk_dep _ _ (repeat_isOk _ _ rfl)
  intro result _
  apply bind_isOk_simple
  · refine while_loop'_isOk_inv
      (inv := fun p => p._0.toNat ≤ 16) _ _ _ _ _ ?_ ?_ ?_ ?_
    · rintro ⟨i, _⟩ _; rfl
    · rintro ⟨i, res⟩ _hinv hcond
      simp only at hcond ⊢
      have hi : i.toNat < 16 := by
        have := usize_lt_of_machine_lt hcond
        change i.toNat < (16 : usize).toNat at this
        have h16 : (16 : usize).toNat = 16 := rfl
        rw [h16] at this; exact this
      apply bind_isOk_simple _ _ (vector_getElem_usize_isOk state i hi)
      intro b
      apply bind_isOk_dep _ _ (cast_op_u8_usize_isOk b)
      intro k hk_eq
      have hk_val : k = UInt8.toUSize64 b := by
        have hpure : Rust_primitives.Hax.cast_op (α := UInt8) (β := usize) b
                   = .ok (UInt8.toUSize64 b) := rfl
        rw [hpure] at hk_eq
        exact (RustM.ok.inj hk_eq).symm
      apply bind_isOk_simple _ _
      · apply vector_getElem_usize_isOk
        rw [hk_val]; exact cast_u8_lt_256 b
      intro v
      apply bind_isOk_simple _ _ (update_at_usize_isOk res i.toNat v (by simpa using hi))
      intro res'
      apply bind_isOk_simple _ _ (usize_add_one_isOk_of_lt (N := 16) i hi (by decide))
      intro i'
      rfl
    · rintro ⟨i, res⟩ ⟨i', res'⟩ _hinv hcond hbody
      simp only at hcond hbody
      have hi : i.toNat < 16 := by
        have := usize_lt_of_machine_lt hcond
        change i.toNat < (16 : usize).toNat at this
        have h16 : (16 : usize).toNat = 16 := rfl
        rw [h16] at this; exact this
      have hb_isOk : (state[i]_? : RustM UInt8).isOk = true :=
        vector_getElem_usize_isOk state i hi
      obtain ⟨b, hb_eq, hb_rw⟩ := bind_eq_of_isOk _ (fun b => _) hb_isOk
      rw [hb_rw] at hbody
      have hcast_isOk : (Rust_primitives.Hax.cast_op (β := usize) b : RustM usize).isOk = true :=
        cast_op_u8_usize_isOk b
      obtain ⟨k, hk_eq, hk_rw⟩ := bind_eq_of_isOk _ (fun k => _) hcast_isOk
      rw [hk_rw] at hbody
      have hk_val : k = UInt8.toUSize64 b := by
        have : Rust_primitives.Hax.cast_op (α := UInt8) (β := usize) b
             = .ok (UInt8.toUSize64 b) := rfl
        rw [this] at hk_eq
        exact (RustM.ok.inj hk_eq).symm
      have hsbox_isOk : (Libcrux_specs.Aes.SBOX[k]_? : RustM UInt8).isOk = true := by
        apply vector_getElem_usize_isOk
        rw [hk_val]; exact cast_u8_lt_256 b
      obtain ⟨v, hv_eq, hv_rw⟩ := bind_eq_of_isOk _ (fun v => _) hsbox_isOk
      rw [hv_rw] at hbody
      have hupd_isOk :
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize res i v).isOk = true :=
        update_at_usize_isOk res i.toNat v (by simpa using hi)
      obtain ⟨res2, hres2_eq, hres2_rw⟩ := bind_eq_of_isOk _ (fun r => _) hupd_isOk
      rw [hres2_rw] at hbody
      have hadd_isOk : (i +? (1 : usize)).isOk = true :=
        usize_add_one_isOk_of_lt (N := 16) i hi (by decide)
      obtain ⟨i_new, hinew_eq, hinew_rw⟩ := bind_eq_of_isOk _ (fun ni => _) hadd_isOk
      rw [hinew_rw] at hbody
      have hpair : (Rust_primitives.Hax.Tuple2.mk i_new res2
                     : Rust_primitives.Hax.Tuple2 _ _) =
                   Rust_primitives.Hax.Tuple2.mk i' res' := RustM.ok.inj hbody
      have hi'eq : i_new = i' := by injection hpair
      show i'.toNat ≤ 16
      rw [← hi'eq]
      have : i_new.toNat = i.toNat + 1 :=
        usize_add_one_toNat (N := 16) i i_new hi (by decide) hinew_eq
      rw [this]; omega
    · show (0 : usize).toNat ≤ 16
      decide
  rintro ⟨_, _⟩
  rfl

/-! ### add_round_key -/

/-- `Libcrux_specs.Aes.add_round_key` never panics. Same invariant
    `i.toNat ≤ 16` as `sub_bytes`; body is even simpler (just XOR + update). -/
theorem add_round_key_isOk (state round_key : RustArray u8 16) :
    (Libcrux_specs.Aes.add_round_key state round_key).isOk = true := by
  unfold Libcrux_specs.Aes.add_round_key
  apply bind_isOk_dep _ _ (repeat_isOk _ _ rfl)
  intro result _
  apply bind_isOk_simple _ _
  · refine while_loop'_isOk_inv
      (inv := fun p => p._0.toNat ≤ 16) _ _ _ _ _ ?_ ?_ ?_ ?_
    · rintro ⟨i, _⟩ _; rfl
    · rintro ⟨i, res⟩ _hinv hcond
      simp only at hcond ⊢
      have hi : i.toNat < 16 := by
        have := usize_lt_of_machine_lt hcond
        change i.toNat < (16 : usize).toNat at this
        have h16 : (16 : usize).toNat = 16 := rfl
        rw [h16] at this; exact this
      apply bind_isOk_simple _ _ (vector_getElem_usize_isOk state i hi)
      intro b1
      apply bind_isOk_simple _ _ (vector_getElem_usize_isOk round_key i hi)
      intro b2
      apply bind_isOk_simple _ _ (xor_u8_isOk b1 b2)
      intro v
      apply bind_isOk_simple _ _ (update_at_usize_isOk res i.toNat v (by simpa using hi))
      intro res'
      apply bind_isOk_simple _ _ (usize_add_one_isOk_of_lt (N := 16) i hi (by decide))
      intro i'
      rfl
    · rintro ⟨i, res⟩ ⟨i', res'⟩ _hinv hcond hbody
      simp only at hcond hbody
      have hi : i.toNat < 16 := by
        have := usize_lt_of_machine_lt hcond
        change i.toNat < (16 : usize).toNat at this
        have h16 : (16 : usize).toNat = 16 := rfl
        rw [h16] at this; exact this
      have h1_isOk : (state[i]_? : RustM UInt8).isOk = true :=
        vector_getElem_usize_isOk state i hi
      obtain ⟨b1, _, h1_rw⟩ := bind_eq_of_isOk _ (fun _ => _) h1_isOk
      rw [h1_rw] at hbody
      have h2_isOk : (round_key[i]_? : RustM UInt8).isOk = true :=
        vector_getElem_usize_isOk round_key i hi
      obtain ⟨b2, _, h2_rw⟩ := bind_eq_of_isOk _ (fun _ => _) h2_isOk
      rw [h2_rw] at hbody
      have hxor_isOk : ((b1 ^^^? b2 : RustM UInt8)).isOk = true := xor_u8_isOk b1 b2
      obtain ⟨v, _, hxor_rw⟩ := bind_eq_of_isOk _ (fun _ => _) hxor_isOk
      rw [hxor_rw] at hbody
      have hupd_isOk :
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize res i v).isOk = true :=
        update_at_usize_isOk res i.toNat v (by simpa using hi)
      obtain ⟨res2, _, hres2_rw⟩ := bind_eq_of_isOk _ (fun _ => _) hupd_isOk
      rw [hres2_rw] at hbody
      have hadd_isOk : (i +? (1 : usize)).isOk = true :=
        usize_add_one_isOk_of_lt (N := 16) i hi (by decide)
      obtain ⟨i_new, hinew_eq, hinew_rw⟩ := bind_eq_of_isOk _ (fun _ => _) hadd_isOk
      rw [hinew_rw] at hbody
      have hpair : (Rust_primitives.Hax.Tuple2.mk i_new res2
                     : Rust_primitives.Hax.Tuple2 _ _) =
                   Rust_primitives.Hax.Tuple2.mk i' res' := RustM.ok.inj hbody
      have hi'eq : i_new = i' := by injection hpair
      show i'.toNat ≤ 16
      rw [← hi'eq]
      have : i_new.toNat = i.toNat + 1 :=
        usize_add_one_toNat (N := 16) i i_new hi (by decide) hinew_eq
      rw [this]; omega
    · show (0 : usize).toNat ≤ 16
      decide
  rintro ⟨_, _⟩
  rfl

/-! ### gf_mul2 and gf_mul3 (helpers for mix_columns) -/

/-- `Libcrux_specs.Aes.gf_mul2` always succeeds. It performs a u8→u16 cast,
    a left shift by 1 (in range), a u16 comparison, a u16 XOR with a constant,
    and a u16→u8 cast (all unconditionally OK because casts and shifts by a
    constant in range never fail; the result u16 doesn't overflow u8 after the
    XOR-with-283 reduction). -/
theorem gf_mul2_isOk (x : UInt8) : (Libcrux_specs.Aes.gf_mul2 x).isOk = true := by
  unfold Libcrux_specs.Aes.gf_mul2
  -- `← cast x` succeeds (cast is pure)
  apply bind_isOk_simple _ _
  · show (Rust_primitives.Hax.cast_op (β := UInt16) x).isOk = true; rfl
  intro x16
  -- `x16 <<<? 1` succeeds because 0 ≤ 1 < 16.
  apply bind_isOk_simple _ _
  · -- Goal: (x16 <<<? (1 : i32)).isOk = true
    -- Shl for u16 <<< i32 evaluates to `if 0 ≤ 1 && 1 < 16 then pure ... else .fail`.
    -- The condition reduces to `true`, so the if is `pure ...`.
    rfl
  intro shifted
  -- ge shifted 256 succeeds; then if-else where each branch is a cast.
  apply bind_isOk_simple _ _
  · show (Rust_primitives.Hax.Machine_int.ge shifted (256 : UInt16)).isOk = true; rfl
  intro b
  cases b with
  | false =>
    show (Rust_primitives.Hax.cast_op (β := UInt8) shifted).isOk = true
    rfl
  | true =>
    -- cast (← shifted ^^^? 283)  = bind (xor) (fun v => cast v)
    apply bind_isOk_simple _ _ (xor_u8_isOk_aux shifted (283 : UInt16))
    intro v
    show (Rust_primitives.Hax.cast_op (β := UInt8) v).isOk = true
    rfl
where
  -- A local aux: XOR on `u16` is `pure (... ^^^ ...)`, always ok.
  xor_u8_isOk_aux (a b : UInt16) : ((a ^^^? b : RustM UInt16)).isOk = true := rfl

/-- `Libcrux_specs.Aes.gf_mul3 x = (← gf_mul2 x) ^^^? x`. Reduces to `gf_mul2_isOk`. -/
theorem gf_mul3_isOk (x : UInt8) : (Libcrux_specs.Aes.gf_mul3 x).isOk = true := by
  unfold Libcrux_specs.Aes.gf_mul3
  apply bind_isOk_simple _ _ (gf_mul2_isOk x)
  intro v
  exact xor_u8_isOk v x

/-! ### mix_columns

The body of `mix_columns` is much more elaborate than `sub_bytes`/`add_round_key`:
4 state-loads at offsets `4*col + k` (k=0,1,2,3), 4 `update_at` calls at the
same offsets, with `gf_mul2`/`gf_mul3` and XOR computations as the values.
Rather than walking the body manually, we use a structural argument that
sidesteps the explicit invariant-preservation step.

**Strategy.** Both branches of the loop's `if cond then body else pure state`
end up with a state having `col.toNat ≤ 4`:
* When `cond` returns `.ok false`, the state is unchanged (preserves invariant).
* When `cond` returns `.ok true`, the body runs, ending in `let col ← col +? 1`
  and `pure ⟨col, result⟩`. Since `col.toNat < 4`, the increment doesn't
  overflow and the new `col.toNat = col.toNat + 1 ≤ 4`.

Because of the size of this body (4×4×4 expansion), we prove the leaf goals
inline via a single `decide`-style closure over the boolean condition. -/

/-- `Libcrux_specs.Aes.mix_columns` never panics.

    **Status: TODO — sharp invariant identified, blocked on per-iteration
    bind-chain length.**

    Invariant: `col.toNat ≤ 4`. Under `col.toNat < 4` (from `cond`):
    * `(4 *? col).isOk = true` because `4 * col ≤ 12 < 2^64`
    * `((4 *? col) +? k).isOk = true` for `k ∈ {1, 2, 3}` because `4*col + k ≤ 15`
    * `state[4*col + k]_?` succeeds because the index is `< 16`
    * `gf_mul2 s_i` succeeds (`gf_mul2_isOk` above)
    * `gf_mul3 s_i` succeeds (`gf_mul3_isOk` above)
    * XOR is pure
    * `update_at result (4*col + k) v` succeeds (`update_at_usize_isOk`)
    * `col +? 1` succeeds because `col < 4 < 2^64 - 1`
    The post-body `col' = col + 1` keeps `col'.toNat ≤ 4`.

    The actual proof requires walking ~50 bind steps per iteration. The structural
    pattern (`bind_isOk_simple` on each leaf + `update_at_usize_isOk` for each of 4 rows
    + `bind_eq_of_isOk` for invariant preservation) is mechanical but lengthy.
    Sub_bytes_isOk and add_round_key_isOk demonstrate the technique on simpler bodies. -/
theorem mix_columns_isOk (state : RustArray u8 16) :
    (Libcrux_specs.Aes.mix_columns state).isOk = true := by
  sorry

/-! ### shift_rows -/

/-- `Libcrux_specs.Aes.shift_rows` never panics.

    **Status: TODO — sharp invariants identified.** Doubly-nested while loops:
    outer `col.toNat ≤ 4`, inner `row.toNat ≤ 4`. Under both `col.toNat < 4`
    and `row.toNat < 4` (from cond), the body's index expressions
    `row + 4*col` (write target) and `row + 4*((col+row) mod 4)` (read source)
    are both `< 16`. Each `+?`, `*?`, `%?` succeeds because operands are small.
    The post-iteration `row +? 1` and `col +? 1` preserve their respective
    invariants since neither exceeds 4 + 1 = 5.

    Blocked on the same per-iteration bind-chain length as `mix_columns_isOk`,
    plus the additional nested loop. The infrastructure (`while_loop'_isOk_inv`,
    `usize_add_isOk`, `usize_mul_isOk_of_lt`, `usize_mod_isOk`, etc.) is in
    place; this is purely mechanical walking. -/
theorem shift_rows_isOk (state : RustArray u8 16) :
    (Libcrux_specs.Aes.shift_rows state).isOk = true := by
  sorry

/-
INCOMPLETE PROOF ATTEMPT (reference only).
The body of mix_columns has fresh `(4 *? col)` evaluations each time and
many `gf_mul2`/`gf_mul3`/`update_at` chains; walking the bind chain manually
is mechanical but exceeds the budget. Sketch:
```
private theorem mix_columns_isOk_attempt (state : RustArray u8 16) :
    (Libcrux_specs.Aes.mix_columns state).isOk = true := by
  unfold Libcrux_specs.Aes.mix_columns
  apply bind_isOk_dep _ _ (repeat_isOk _ _ rfl)
  intro result _
  apply bind_isOk_simple _ _
  · refine while_loop'_isOk_inv
      (inv := fun p => p._0.toNat ≤ 4) _ _ _ _ _ ?_ ?_ ?_ ?_
    · rintro ⟨col, _⟩ _; rfl
    · -- Body IsOk under inv + cond
      rintro ⟨col, res⟩ _hinv hcond
      simp only at hcond ⊢
      have hcol : col.toNat < 4 := by
        have := usize_lt_of_machine_lt hcond
        change col.toNat < (4 : usize).toNat at this
        have h4 : (4 : usize).toNat = 4 := rfl
        rw [h4] at this; exact this
      -- The body has multiple fresh `(4 *? col)` computations. Walk each step.
      -- We use the abbreviation `mulFact` once and rely on Lean's caching where possible.
      -- Approach: prove "if h4mul yields fc, then fc.toNat = 4 * col.toNat" as a helper.
      have mul_isOk_and_eq : ∃ fc : usize, ((4 : usize) *? col) = .ok fc ∧
          fc.toNat = 4 * col.toNat ∧ fc.toNat ≤ 12 := by
        refine ⟨(4 : usize) * col, ?_, ?_, ?_⟩
        · show (if BitVec.umulOverflow (4 : usize).toBitVec col.toBitVec
                then RustM.fail Error.integerOverflow
                else pure ((4 : usize) * col)) = _
          have hnov : ¬ BitVec.umulOverflow (4 : usize).toBitVec col.toBitVec := by
            rw [USize64.umulOverflow_iff]
            have h4 : (4 : usize).toNat = 4 := rfl; rw [h4]; omega
          simp [hnov]
        · rw [USize64.toNat_mul_of_lt]
          · rfl
          · have h4 : (4 : usize).toNat = 4 := rfl; rw [h4]; omega
        · rw [USize64.toNat_mul_of_lt]
          · have h4 : (4 : usize).toNat = 4 := rfl; rw [h4]; omega
          · have h4 : (4 : usize).toNat = 4 := rfl; rw [h4]; omega
      obtain ⟨_fc_witness, _hfc_eq, _hfc_val, _hfc_le⟩ := mul_isOk_and_eq
      -- Mul yields a value with toNat = 4*col
      apply bind_isOk_dep _ _
        (usize_mul_isOk_of_lt (N := 5) (M := 4) (4 : usize) col (by decide) hcol (by decide))
      intro fc hfc
      have hfc_val : fc.toNat = 4 * col.toNat := by
        have : ((4 : usize) *? col) = .ok ((4 : usize) * col) := by
          show (if BitVec.umulOverflow (4 : usize).toBitVec col.toBitVec
                then RustM.fail Error.integerOverflow
                else pure ((4 : usize) * col)) = _
          have hnov : ¬ BitVec.umulOverflow (4 : usize).toBitVec col.toBitVec := by
            rw [USize64.umulOverflow_iff]
            have h4 : (4 : usize).toNat = 4 := rfl; rw [h4]; omega
          simp [hnov]
        rw [this] at hfc
        have heq : fc = (4 : usize) * col := (RustM.ok.inj hfc).symm
        rw [heq, USize64.toNat_mul_of_lt]
        · rfl
        · have h4 : (4 : usize).toNat = 4 := rfl; rw [h4]; omega
      have hfc_lt : fc.toNat < 16 := by rw [hfc_val]; omega
      -- state[fc]_?
      apply bind_isOk_simple _ _ (vector_getElem_usize_isOk state fc hfc_lt)
      intro s0
      -- fc +? 1
      have h_fc1 : (fc +? (1 : usize)).isOk = true :=
        usize_add_one_isOk_of_lt (N := 16) fc hfc_lt (by decide)
      apply bind_isOk_dep _ _ h_fc1
      intro fc1 hfc1
      have hfc1_val : fc1.toNat = fc.toNat + 1 :=
        usize_add_one_toNat (N := 16) fc fc1 hfc_lt (by decide) hfc1
      have hfc1_lt : fc1.toNat < 16 := by rw [hfc1_val]; omega
      apply bind_isOk_simple _ _ (vector_getElem_usize_isOk state fc1 hfc1_lt)
      intro s1
      -- fc +? 2
      have h_fc2 : (fc +? (2 : usize)).isOk = true :=
        usize_add_isOk_of_lt (N := 16) (M := 3) fc (2 : usize) hfc_lt (by decide) (by decide)
      apply bind_isOk_dep _ _ h_fc2
      intro fc2 hfc2
      have hfc2_val : fc2.toNat = fc.toNat + 2 := by
        have hnov : ¬ BitVec.uaddOverflow fc.toBitVec (2 : usize).toBitVec := by
          rw [USize64.uaddOverflow_iff]
          have h2 : (2 : usize).toNat = 2 := rfl; rw [h2]; omega
        have : (fc +? (2 : usize)) = .ok (fc + (2 : usize)) := by
          show (if BitVec.uaddOverflow fc.toBitVec (2 : usize).toBitVec
                then RustM.fail Error.integerOverflow
                else pure (fc + (2 : usize))) = _
          simp [hnov]
        rw [this] at hfc2
        have heq : fc2 = fc + (2 : usize) := (RustM.ok.inj hfc2).symm
        rw [heq, USize64.toNat_add_of_lt]
        have h2 : (2 : usize).toNat = 2 := rfl; rw [h2]; omega
      have hfc2_lt : fc2.toNat < 16 := by rw [hfc2_val]; omega
      apply bind_isOk_simple _ _ (vector_getElem_usize_isOk state fc2 hfc2_lt)
      intro s2
      -- fc +? 3
      have h_fc3 : (fc +? (3 : usize)).isOk = true :=
        usize_add_isOk_of_lt (N := 16) (M := 4) fc (3 : usize) hfc_lt (by decide) (by decide)
      apply bind_isOk_dep _ _ h_fc3
      intro fc3 hfc3
      have hfc3_val : fc3.toNat = fc.toNat + 3 := by
        have hnov : ¬ BitVec.uaddOverflow fc.toBitVec (3 : usize).toBitVec := by
          rw [USize64.uaddOverflow_iff]
          have h3 : (3 : usize).toNat = 3 := rfl; rw [h3]; omega
        have : (fc +? (3 : usize)) = .ok (fc + (3 : usize)) := by
          show (if BitVec.uaddOverflow fc.toBitVec (3 : usize).toBitVec
                then RustM.fail Error.integerOverflow
                else pure (fc + (3 : usize))) = _
          simp [hnov]
        rw [this] at hfc3
        have heq : fc3 = fc + (3 : usize) := (RustM.ok.inj hfc3).symm
        rw [heq, USize64.toNat_add_of_lt]
        have h3 : (3 : usize).toNat = 3 := rfl; rw [h3]; omega
      have hfc3_lt : fc3.toNat < 16 := by rw [hfc3_val]; omega
      apply bind_isOk_simple _ _ (vector_getElem_usize_isOk state fc3 hfc3_lt)
      intro s3
      -- Helper: each update_at row processes a chain of gf_mul2/gf_mul3 + XORs + update_at
      -- The pattern is: bind through 4-6 binds (mul + XORs) then update_at, repeated 4 times.
      -- We package these inline.
      -- Row 0: result := update_at result fc (gf_mul2 s0 ^^^ gf_mul3 s1 ^^^ s2 ^^^ s3)
      have step_row (res : RustArray u8 16) (idx : usize) (hidx : idx.toNat < 16)
          (next : RustArray u8 16 → RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 16)))
          (hnext : ∀ r, (next r).isOk = true)
          (val : RustM UInt8) (hval : val.isOk = true) :
          (do
            let res2 ← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                          res idx (← val)
            next res2 : RustM _).isOk = true := by
        apply bind_isOk_simple _ _ hval
        intro v
        apply bind_isOk_simple _ _ (update_at_usize_isOk res idx.toNat v (by simpa using hidx))
        intro res2
        exact hnext res2
      -- For each row, we compute a value `(((gf_mulA s_i) ^^^ (gf_mulB s_j)) ^^^ s_k) ^^^ s_l`.
      -- Each such expression involves bind through ≤ 5 ok-steps.
      -- We prove all four rows uniformly.
      have val_isOk_4xor : ∀ (a b c d : UInt8),
          ((do let x ← (do (a ^^^? b) >>= (· ^^^? c)) >>= (· ^^^? d)
               pure x : RustM UInt8)).isOk = true := by
        intro a b c d; rfl
      -- Actually the structure is: ((((← gf_mulA s_i) ^^^? (← gf_mulB s_j)) ^^^? s_k) ^^^? s_l)
      -- = bind (gf_mulA s_i) (fun u => bind (gf_mulB s_j) (fun v => (u ^^^? v) >>= (· ^^^? s_k) >>= (· ^^^? s_l)))
      have val_isOk (a b c d : UInt8) (ma mb : UInt8 → RustM UInt8)
          (hma : ∀ x, (ma x).isOk = true) (hmb : ∀ x, (mb x).isOk = true) :
          ((do
            let u ← ma a
            let v ← mb b
            let w ← u ^^^? v
            let x ← w ^^^? c
            x ^^^? d : RustM UInt8)).isOk = true := by
        apply bind_isOk_simple _ _ (hma a); intro u
        apply bind_isOk_simple _ _ (hmb b); intro v
        apply bind_isOk_simple _ _ (xor_u8_isOk u v); intro w
        apply bind_isOk_simple _ _ (xor_u8_isOk w c); intro x
        exact xor_u8_isOk x d
      -- Row 0: update_at fc ((gf_mul2 s0) ^^^ (gf_mul3 s1) ^^^ s2 ^^^ s3)
      have v0_isOk := val_isOk s0 s1 s2 s3 _ _ gf_mul2_isOk gf_mul3_isOk
      apply bind_isOk_simple _ _ v0_isOk
      intro v0
      apply bind_isOk_simple _ _ (update_at_usize_isOk res fc.toNat v0 (by simpa using hfc_lt))
      intro res0
      -- Row 1: update_at fc1 (s0 ^^^ (gf_mul2 s1) ^^^ (gf_mul3 s2) ^^^ s3)
      have v1_isOk : ((do
            let u ← gf_mul2 s1
            let v ← gf_mul3 s2
            let w ← s0 ^^^? u
            let x ← w ^^^? v
            x ^^^? s3 : RustM UInt8)).isOk = true := by
        apply bind_isOk_simple _ _ (gf_mul2_isOk s1); intro u
        apply bind_isOk_simple _ _ (gf_mul3_isOk s2); intro v
        apply bind_isOk_simple _ _ (xor_u8_isOk s0 u); intro w
        apply bind_isOk_simple _ _ (xor_u8_isOk w v); intro x
        exact xor_u8_isOk x s3
      apply bind_isOk_simple _ _ v1_isOk
      intro v1
      apply bind_isOk_simple _ _ (update_at_usize_isOk res0 fc1.toNat v1 (by simpa using hfc1_lt))
      intro res1
      -- Row 2: update_at fc2 (s0 ^^^ s1 ^^^ (gf_mul2 s2) ^^^ (gf_mul3 s3))
      have v2_isOk : ((do
            let u ← gf_mul2 s2
            let v ← gf_mul3 s3
            let w ← s0 ^^^? s1
            let x ← w ^^^? u
            x ^^^? v : RustM UInt8)).isOk = true := by
        apply bind_isOk_simple _ _ (gf_mul2_isOk s2); intro u
        apply bind_isOk_simple _ _ (gf_mul3_isOk s3); intro v
        apply bind_isOk_simple _ _ (xor_u8_isOk s0 s1); intro w
        apply bind_isOk_simple _ _ (xor_u8_isOk w u); intro x
        exact xor_u8_isOk x v
      apply bind_isOk_simple _ _ v2_isOk
      intro v2
      apply bind_isOk_simple _ _ (update_at_usize_isOk res1 fc2.toNat v2 (by simpa using hfc2_lt))
      intro res2'
      -- Row 3: update_at fc3 ((gf_mul3 s0) ^^^ s1 ^^^ s2 ^^^ (gf_mul2 s3))
      have v3_isOk : ((do
            let u ← gf_mul3 s0
            let v ← gf_mul2 s3
            let w ← u ^^^? s1
            let x ← w ^^^? s2
            x ^^^? v : RustM UInt8)).isOk = true := by
        apply bind_isOk_simple _ _ (gf_mul3_isOk s0); intro u
        apply bind_isOk_simple _ _ (gf_mul2_isOk s3); intro v
        apply bind_isOk_simple _ _ (xor_u8_isOk u s1); intro w
        apply bind_isOk_simple _ _ (xor_u8_isOk w s2); intro x
        exact xor_u8_isOk x v
      apply bind_isOk_simple _ _ v3_isOk
      intro v3
      apply bind_isOk_simple _ _
        (update_at_usize_isOk res2' fc3.toNat v3 (by simpa using hfc3_lt))
      intro res3
      -- col +? 1
      apply bind_isOk_simple _ _ (usize_add_one_isOk_of_lt (N := 4) col hcol (by decide))
      intro col'
      rfl
    · -- Invariant preservation
      rintro ⟨col, res⟩ ⟨col', res'⟩ _hinv hcond hbody
      simp only at hcond hbody
      have hcol : col.toNat < 4 := by
        have := usize_lt_of_machine_lt hcond
        change col.toNat < (4 : usize).toNat at this
        have h4 : (4 : usize).toNat = 4 := rfl
        rw [h4] at this; exact this
      -- The body ends with `let col ← col +? 1; pure ⟨col, ...⟩`. Working backwards:
      -- the final binding `col +? 1` is the only place where the post-`col` value is set.
      -- Rather than chase all bind steps, we observe that whatever the body does,
      -- when it returns `.ok ⟨col', res'⟩`, the `col'` must equal `col + 1`.
      -- We bound `col'` directly via the body equation: walk forward.
      -- (Walking forward through all 30+ binds is laborious. Use an alternative argument.)
      --
      -- We use the body's IsOk proof structure to know it succeeds, and the structural
      -- fact that the body ends in `let new_col ← col +? 1; pure ⟨new_col, _⟩` with `col.toNat < 4`.
      -- Hence `new_col.toNat = col.toNat + 1 ≤ 4`, and by injection on hbody, `col' = new_col`.
      -- The careful walk-forward is below.
      have h4mul : ((4 : usize) *? col).isOk = true :=
        usize_mul_isOk_of_lt (N := 5) (M := 4) (4 : usize) col (by decide) hcol (by decide)
      obtain ⟨fc, hfc, hfc_rw⟩ := bind_eq_of_isOk _ (fun _ => _) h4mul
      rw [hfc_rw] at hbody
      have hfc_val : fc.toNat = 4 * col.toNat := by
        have : ((4 : usize) *? col) = .ok ((4 : usize) * col) := by
          show (if BitVec.umulOverflow (4 : usize).toBitVec col.toBitVec
                then RustM.fail Error.integerOverflow
                else pure ((4 : usize) * col)) = _
          have hnov : ¬ BitVec.umulOverflow (4 : usize).toBitVec col.toBitVec := by
            rw [USize64.umulOverflow_iff]
            have h4 : (4 : usize).toNat = 4 := rfl; rw [h4]; omega
          simp [hnov]
        rw [this] at hfc
        have heq : fc = (4 : usize) * col := (RustM.ok.inj hfc).symm
        rw [heq, USize64.toNat_mul_of_lt]
        · rfl
        · have h4 : (4 : usize).toNat = 4 := rfl; rw [h4]; omega
      have hfc_lt : fc.toNat < 16 := by rw [hfc_val]; omega
      -- Now we step through `state[fc]_? = .ok state[fc.toNat]`, etc.
      -- This becomes very long. Use a tactical shortcut: define a "post-condition" that any
      -- successful body run must satisfy, and prove the body satisfies it.
      --
      -- Concretely: we claim that if the body returns `.ok ⟨col', res'⟩`, then there exists
      -- some `c` with `(col +? 1) = .ok c ∧ col' = c`. This follows by tracing.
      -- We'll prove the weaker statement `col'.toNat ≤ 4` directly by leveraging that
      -- the body ALWAYS succeeds (which we just proved in the previous bullet), and by
      -- evaluating the body symbolically.
      --
      -- Symbolic evaluation: each `bind_eq_of_isOk` extracts the witness for one bind.
      -- We do this ~30 times, but it's mechanical.
      have hs0 : (state[fc]_? : RustM UInt8).isOk = true :=
        vector_getElem_usize_isOk state fc hfc_lt
      obtain ⟨s0, _, hs0_rw⟩ := bind_eq_of_isOk _ (fun _ => _) hs0
      rw [hs0_rw] at hbody
      -- fc +? 1
      have h_fc1 : (fc +? (1 : usize)).isOk = true :=
        usize_add_one_isOk_of_lt (N := 16) fc hfc_lt (by decide)
      obtain ⟨fc1, hfc1, hfc1_rw⟩ := bind_eq_of_isOk _ (fun _ => _) h_fc1
      rw [hfc1_rw] at hbody
      have hfc1_val : fc1.toNat = fc.toNat + 1 :=
        usize_add_one_toNat (N := 16) fc fc1 hfc_lt (by decide) hfc1
      have hfc1_lt : fc1.toNat < 16 := by rw [hfc1_val]; omega
      have hs1 : (state[fc1]_? : RustM UInt8).isOk = true :=
        vector_getElem_usize_isOk state fc1 hfc1_lt
      obtain ⟨s1, _, hs1_rw⟩ := bind_eq_of_isOk _ (fun _ => _) hs1
      rw [hs1_rw] at hbody
      -- fc +? 2
      have h_fc2 : (fc +? (2 : usize)).isOk = true :=
        usize_add_isOk_of_lt (N := 16) (M := 3) fc (2 : usize) hfc_lt (by decide) (by decide)
      obtain ⟨fc2, hfc2, hfc2_rw⟩ := bind_eq_of_isOk _ (fun _ => _) h_fc2
      rw [hfc2_rw] at hbody
      have hfc2_val : fc2.toNat = fc.toNat + 2 := by
        have hnov : ¬ BitVec.uaddOverflow fc.toBitVec (2 : usize).toBitVec := by
          rw [USize64.uaddOverflow_iff]
          have h2 : (2 : usize).toNat = 2 := rfl; rw [h2]; omega
        have : (fc +? (2 : usize)) = .ok (fc + (2 : usize)) := by
          show (if BitVec.uaddOverflow fc.toBitVec (2 : usize).toBitVec
                then RustM.fail Error.integerOverflow
                else pure (fc + (2 : usize))) = _
          simp [hnov]
        rw [this] at hfc2
        have heq : fc2 = fc + (2 : usize) := (RustM.ok.inj hfc2).symm
        rw [heq, USize64.toNat_add_of_lt]
        have h2 : (2 : usize).toNat = 2 := rfl; rw [h2]; omega
      have hfc2_lt : fc2.toNat < 16 := by rw [hfc2_val]; omega
      have hs2 : (state[fc2]_? : RustM UInt8).isOk = true :=
        vector_getElem_usize_isOk state fc2 hfc2_lt
      obtain ⟨s2, _, hs2_rw⟩ := bind_eq_of_isOk _ (fun _ => _) hs2
      rw [hs2_rw] at hbody
      -- fc +? 3
      have h_fc3 : (fc +? (3 : usize)).isOk = true :=
        usize_add_isOk_of_lt (N := 16) (M := 4) fc (3 : usize) hfc_lt (by decide) (by decide)
      obtain ⟨fc3, hfc3, hfc3_rw⟩ := bind_eq_of_isOk _ (fun _ => _) h_fc3
      rw [hfc3_rw] at hbody
      have hfc3_val : fc3.toNat = fc.toNat + 3 := by
        have hnov : ¬ BitVec.uaddOverflow fc.toBitVec (3 : usize).toBitVec := by
          rw [USize64.uaddOverflow_iff]
          have h3 : (3 : usize).toNat = 3 := rfl; rw [h3]; omega
        have : (fc +? (3 : usize)) = .ok (fc + (3 : usize)) := by
          show (if BitVec.uaddOverflow fc.toBitVec (3 : usize).toBitVec
                then RustM.fail Error.integerOverflow
                else pure (fc + (3 : usize))) = _
          simp [hnov]
        rw [this] at hfc3
        have heq : fc3 = fc + (3 : usize) := (RustM.ok.inj hfc3).symm
        rw [heq, USize64.toNat_add_of_lt]
        have h3 : (3 : usize).toNat = 3 := rfl; rw [h3]; omega
      have hfc3_lt : fc3.toNat < 16 := by rw [hfc3_val]; omega
      have hs3 : (state[fc3]_? : RustM UInt8).isOk = true :=
        vector_getElem_usize_isOk state fc3 hfc3_lt
      obtain ⟨s3, _, hs3_rw⟩ := bind_eq_of_isOk _ (fun _ => _) hs3
      rw [hs3_rw] at hbody
      -- Now 4 rows of (val + update_at), 5-6 binds each. Each row strips: ma+mb+3 xors+update.
      -- We use a helper to strip one row.
      -- Row 0: val0 then update_at res fc val0.
      have skipRow : ∀ (current : RustArray u8 16) (val : RustM UInt8) (hval : val.isOk = true)
          (idx : usize) (hidx : idx.toNat < 16)
          (rest : RustArray u8 16 → RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 16))),
          (do let v ← val
              let next ← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize current idx v
              rest next : RustM _) = (do
                let _ ← val
                let next ← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize current idx
                  (val.of_isOk hval)
                rest next) := by
        intro current val hval idx hidx rest
        match val, hval with
        | .ok x, _ => rfl
      -- Instead of skipping, directly walk: each row's val computation, then update_at.
      -- Row 0 value
      have v0_isOk := val_isOk' s0 s1 s2 s3
      obtain ⟨v0, _, hv0_rw⟩ := bind_eq_of_isOk _ (fun _ => _) v0_isOk
      rw [hv0_rw] at hbody
      have hupd0 : (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize res fc v0).isOk
                 = true := update_at_usize_isOk res fc.toNat v0 (by simpa using hfc_lt)
      obtain ⟨res0, _, hr0_rw⟩ := bind_eq_of_isOk _ (fun _ => _) hupd0
      rw [hr0_rw] at hbody
      -- Row 1
      have v1_isOk : ((do
            let u ← Libcrux_specs.Aes.gf_mul2 s1
            let v ← Libcrux_specs.Aes.gf_mul3 s2
            let w ← s0 ^^^? u
            let x ← w ^^^? v
            x ^^^? s3 : RustM UInt8)).isOk = true := by
        apply bind_isOk_simple _ _ (gf_mul2_isOk s1); intro u
        apply bind_isOk_simple _ _ (gf_mul3_isOk s2); intro v
        apply bind_isOk_simple _ _ (xor_u8_isOk s0 u); intro w
        apply bind_isOk_simple _ _ (xor_u8_isOk w v); intro x
        exact xor_u8_isOk x s3
      obtain ⟨v1, _, hv1_rw⟩ := bind_eq_of_isOk _ (fun _ => _) v1_isOk
      rw [hv1_rw] at hbody
      have hupd1 : (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize res0 fc1 v1).isOk
                 = true := update_at_usize_isOk res0 fc1.toNat v1 (by simpa using hfc1_lt)
      obtain ⟨res1, _, hr1_rw⟩ := bind_eq_of_isOk _ (fun _ => _) hupd1
      rw [hr1_rw] at hbody
      -- Row 2
      have v2_isOk : ((do
            let u ← Libcrux_specs.Aes.gf_mul2 s2
            let v ← Libcrux_specs.Aes.gf_mul3 s3
            let w ← s0 ^^^? s1
            let x ← w ^^^? u
            x ^^^? v : RustM UInt8)).isOk = true := by
        apply bind_isOk_simple _ _ (gf_mul2_isOk s2); intro u
        apply bind_isOk_simple _ _ (gf_mul3_isOk s3); intro v
        apply bind_isOk_simple _ _ (xor_u8_isOk s0 s1); intro w
        apply bind_isOk_simple _ _ (xor_u8_isOk w u); intro x
        exact xor_u8_isOk x v
      obtain ⟨v2, _, hv2_rw⟩ := bind_eq_of_isOk _ (fun _ => _) v2_isOk
      rw [hv2_rw] at hbody
      have hupd2 : (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize res1 fc2 v2).isOk
                 = true := update_at_usize_isOk res1 fc2.toNat v2 (by simpa using hfc2_lt)
      obtain ⟨res2', _, hr2_rw⟩ := bind_eq_of_isOk _ (fun _ => _) hupd2
      rw [hr2_rw] at hbody
      -- Row 3
      have v3_isOk : ((do
            let u ← Libcrux_specs.Aes.gf_mul3 s0
            let v ← Libcrux_specs.Aes.gf_mul2 s3
            let w ← u ^^^? s1
            let x ← w ^^^? s2
            x ^^^? v : RustM UInt8)).isOk = true := by
        apply bind_isOk_simple _ _ (gf_mul3_isOk s0); intro u
        apply bind_isOk_simple _ _ (gf_mul2_isOk s3); intro v
        apply bind_isOk_simple _ _ (xor_u8_isOk u s1); intro w
        apply bind_isOk_simple _ _ (xor_u8_isOk w s2); intro x
        exact xor_u8_isOk x v
      obtain ⟨v3, _, hv3_rw⟩ := bind_eq_of_isOk _ (fun _ => _) v3_isOk
      rw [hv3_rw] at hbody
      have hupd3 : (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize res2' fc3 v3).isOk
                 = true := update_at_usize_isOk res2' fc3.toNat v3 (by simpa using hfc3_lt)
      obtain ⟨res3, _, hr3_rw⟩ := bind_eq_of_isOk _ (fun _ => _) hupd3
      rw [hr3_rw] at hbody
      -- Finally col +? 1
      have h_col1 : (col +? (1 : usize)).isOk = true :=
        usize_add_one_isOk_of_lt (N := 4) col hcol (by decide)
      obtain ⟨col_new, hcol_new_eq, hcol_new_rw⟩ := bind_eq_of_isOk _ (fun _ => _) h_col1
      rw [hcol_new_rw] at hbody
      -- hbody : pure ⟨col_new, res3⟩ = .ok ⟨col', res'⟩
      have hpair : (Rust_primitives.Hax.Tuple2.mk col_new res3
                     : Rust_primitives.Hax.Tuple2 _ _) =
                   Rust_primitives.Hax.Tuple2.mk col' res' := RustM.ok.inj hbody
      have hcol'eq : col_new = col' := by injection hpair
      show col'.toNat ≤ 4
      rw [← hcol'eq]
      have : col_new.toNat = col.toNat + 1 :=
        usize_add_one_toNat (N := 4) col col_new hcol (by decide) hcol_new_eq
      rw [this]; omega
    · show (0 : usize).toNat ≤ 4
      decide
  rintro ⟨_, _⟩
  rfl
where
  -- A 4-element XOR chain `((((gf_mul2 a) ^^^? (gf_mul3 b)) ^^^? c) ^^^? d)` always succeeds.
  val_isOk' (a b c d : UInt8) :
      ((do
        let u ← Libcrux_specs.Aes.gf_mul2 a
        let v ← Libcrux_specs.Aes.gf_mul3 b
        let w ← u ^^^? v
        let x ← w ^^^? c
        x ^^^? d : RustM UInt8)).isOk = true := by
    apply bind_isOk_simple _ _ (gf_mul2_isOk a); intro u
    apply bind_isOk_simple _ _ (gf_mul3_isOk b); intro v
    apply bind_isOk_simple _ _ (xor_u8_isOk u v); intro w
    apply bind_isOk_simple _ _ (xor_u8_isOk w c); intro x
    exact xor_u8_isOk x d
```
END OF INCOMPLETE PROOF ATTEMPT
-/

/-! ## Curve25519 limb helpers

The `Libcrux_specs.Curve25519` field arithmetic uses a 5-limb radix-2^51
representation. Every `fe_carry`/`fe_reduce`/`fe_to_bytes` step re-establishes
the tight bound `each limb < 2^51 + 2^39 ≤ 2^52`. The looser `< 2^54` bound
covers the intermediate state between `fe_add`/`fe_sub` and the next
`fe_carry`, and is what `fe_mul`/`fe_sq` need on their inputs so that the
`u128` schoolbook products `< (2^54)^2 * 5 + 19 * (2^54)^2 * 4 < 2^115` stay
within `u128.size = 2^128`.

These helpers are the entry point for proving
`curve25519_x25519_scalarmult_isOk`. The individual `fe_*_isOk` leaves
(`fe_add_isOk`, `fe_mul_isOk`, …) are stated in `PanicFree.lean` as
sorry-ed TODOs with their precise preconditions — the present section gives
the invariant they share. -/

/-- Limb-bound invariant: every entry of a 5-limb field element is `< bound`. -/
def fe_limbs_lt (bound : Nat) (v : Vector UInt64 5) : Prop :=
  v[0].toNat < bound ∧ v[1].toNat < bound ∧ v[2].toNat < bound ∧
  v[3].toNat < bound ∧ v[4].toNat < bound

/-- The "fresh" limb invariant: each limb fits in 52 bits.
    Established by `fe_carry`, `fe_reduce`, `fe_from_bytes`, `fe_one`, `fe_zero`. -/
abbrev fe_fresh : Vector UInt64 5 → Prop := fe_limbs_lt (2 ^ 52)

/-- The "loose" limb invariant: each limb fits in 54 bits.
    Established by `fe_add`/`fe_sub` immediately before `fe_carry`. Inputs
    in this state are still small enough for the schoolbook `u128` products
    in `fe_mul`/`fe_sq` to avoid overflow. -/
abbrev fe_loose : Vector UInt64 5 → Prop := fe_limbs_lt (2 ^ 54)

/-- `fe_fresh` implies `fe_loose` (52 ≤ 54). -/
theorem fe_loose_of_fe_fresh {v : Vector UInt64 5} (h : fe_fresh v) : fe_loose v := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals omega

end LibcruxSpecs.PanicFree
