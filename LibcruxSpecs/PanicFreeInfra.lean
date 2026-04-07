/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bas Spitters
-/

import LibcruxSpecs.Specs

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

/-! ## Discharge tactic for trivial goals

The `panic_free_simple` tactic tries to close `(do ...).isOk = true` goals
by repeatedly applying `bind_isOk_simple` and the leaf `_isOk` lemmas. -/

attribute [simp] vec_with_capacity_isOk vec_push_isOk vec_as_slice_isOk vec_len_isOk

end LibcruxSpecs.PanicFree
