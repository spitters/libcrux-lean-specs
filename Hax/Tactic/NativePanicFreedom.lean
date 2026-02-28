import Hax.Rust_primitives.RustM

/-!
# Native Panic Freedom

Infrastructure for proving panic freedom of `RustM` computations using `native_decide`
exhaustive evaluation.

## When to use

Use this when `hax_bv_decide` fails due to:
- **u64 arithmetic chains**: kernel deep recursion in the `BVRustM` encoding
- **Cross-type shifts**: `bv_decide` abstracts `(n:UInt8).toNat.toUInt64` as opaque variables
- Any computation where the input type is finite and small enough for exhaustive evaluation
  (u8: 256 values, u16: 65536 values)

## Proof pattern

### 1. Define a Bool-valued checker for success

```lean
private def f_is_ok (args...) : Bool :=
  match f args... with | .ok _ => true | _ => false
```

### 2. Prove exhaustive success via `native_decide`

For each concrete parameter value, enumerate all possible inputs:
```lean
private theorem f_ok_4 :
    ∀ i : Fin 65536, f_is_ok 4 (UInt16.ofBitVec (BitVec.ofFin i)) = true := by native_decide
```

### 3. Assemble the Hoare triple

```lean
@[spec]
theorem f.spec (coefficient_bits : u8) (fe : u16)
    (hcb : coefficient_bits = 4 ∨ coefficient_bits = 5)
    (hfe : fe.toNat < 3329) :
    ⦃ ⌜ True ⌝ ⦄ f coefficient_bits fe ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  apply RustM.triple_true_of_isOk
  rw [UInt16.eq_ofBitVec_toFin fe]
  rcases hcb with rfl | rfl
  · exact f_ok_4 fe.toBitVec.toFin
  · exact f_ok_5 fe.toBitVec.toFin
```

## Performance

- **u8 enumeration** (~256 values): typically < 1 second per case
- **u16 enumeration** (~65536 values): typically 1-5 minutes per case
- **u32/u64**: infeasible (4 billion+ values) — use `hax_bv_decide` or manual proof instead
-/

open Std.Do
open Std.Tactic

namespace RustM

/-- If `f.isOk = true`, then `f` returns some value. -/
theorem exists_ok_of_isOk {α} {f : RustM α} (h : f.isOk = true) :
    ∃ v, f = .ok v := by
  match f, h with
  | .ok v, _ => exact ⟨v, rfl⟩

/-- If `f = .ok v` for some `v`, then the trivial Hoare triple holds. -/
theorem triple_true_of_ok {α} {f : RustM α} (h : ∃ v, f = .ok v) :
    ⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  obtain ⟨v, hv⟩ := h; subst hv; mvcgen

/-- Combined lifting: `isOk = true` implies the trivial Hoare triple.
    Main entry point for `native_decide`-based panic freedom proofs. -/
theorem triple_true_of_isOk {α} {f : RustM α} (h : f.isOk = true) :
    ⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  triple_true_of_ok (exists_ok_of_isOk h)

end RustM

section UIntRoundtrip

/-- Roundtrip: reconstructing a `UInt8` from its `BitVec` representation via `Fin`. -/
@[simp]
theorem UInt8.ofBitVec_toFin_eq (x : UInt8) :
    UInt8.ofBitVec (BitVec.ofFin x.toBitVec.toFin) = x := by simp

/-- Roundtrip (rewrite direction): a `UInt8` equals its `BitVec`/`Fin` reconstruction.
    Useful for rewriting a `UInt8` variable into a form compatible with `∀ i : Fin 256, ...`. -/
theorem UInt8.eq_ofBitVec_toFin (x : UInt8) :
    x = UInt8.ofBitVec (BitVec.ofFin x.toBitVec.toFin) := by simp

/-- Roundtrip: reconstructing a `UInt16` from its `BitVec` representation via `Fin`. -/
@[simp]
theorem UInt16.ofBitVec_toFin_eq (fe : UInt16) :
    UInt16.ofBitVec (BitVec.ofFin fe.toBitVec.toFin) = fe := by simp

/-- Roundtrip (rewrite direction): a `UInt16` equals its `BitVec`/`Fin` reconstruction.
    Useful for rewriting a `UInt16` variable into a form compatible with `∀ i : Fin 65536, ...`. -/
theorem UInt16.eq_ofBitVec_toFin (fe : UInt16) :
    fe = UInt16.ofBitVec (BitVec.ofFin fe.toBitVec.toFin) := by simp

end UIntRoundtrip
