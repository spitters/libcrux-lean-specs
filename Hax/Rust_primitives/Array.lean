
import Hax.Rust_primitives.RustM
import Hax.Rust_primitives.Num
import Hax.Rust_primitives.Range
import Hax.Rust_primitives.Vec

open Std.Do

set_option mvcgen.warning false

/-

# Arrays

Rust arrays, are represented as Lean `Vector` (Lean Arrays of known size)

-/
section RustArray


abbrev RustArray := Vector


inductive Core_models.Array.TryFromSliceError where
  | array.TryFromSliceError

/-- Typeclass for types that support index-based update (Vector, Array/Slice). -/
class RustSetAt (C : Type) (V : outParam Type) where
  setAt : C → Nat → V → RustM C

instance {α n} : RustSetAt (Vector α n) α where
  setAt a i v := if h: i < a.size then pure (Vector.set a i v) else .fail (.arrayOutOfBounds)

instance (priority := low) {α} : RustSetAt (Array α) α where
  setAt a i v := if h: i < a.size then pure (a.setIfInBounds i v) else .fail (.arrayOutOfBounds)

def Rust_primitives.Hax.Monomorphized_update_at.update_at_usize {C V} [RustSetAt C V]
  (a: C) (i:Nat) (v:V) : RustM C := RustSetAt.setAt a i v

@[spec]
theorem Rust_primitives.Hax.Monomorphized_update_at.update_at_usize.spec
  {α n} (a: Vector α n) (i:Nat) (v:α) (h: i < a.size) :
  ⦃ ⌜ True ⌝ ⦄
  (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a i v)
  ⦃ ⇓ r => ⌜ r = Vector.set a i v ⌝ ⦄ := by
  mvcgen [Rust_primitives.Hax.Monomorphized_update_at.update_at_usize, RustSetAt.setAt]


@[spec]
def Rust_primitives.Hax.update_at {α n} (m : Vector α n) (i : Nat) (v : α) : RustM (Vector α n) :=
  if i < n then
    pure ( Vector.setIfInBounds m i v)
  else
    .fail (.arrayOutOfBounds)

@[spec]
def Rust_primitives.Hax.repeat
  {α int_type: Type}
  {n: Nat} [ToNat int_type]
  (v:α) (size:int_type) : RustM (Vector α n)
  :=
  if (n = ToNat.toNat size) then
    pure (Vector.replicate n v)
  else
    .fail Error.arrayOutOfBounds

@[spec]
def Rust_primitives.unsize {α n} (a: Vector α n) : RustM (Array α) :=
  pure (a.toArray)

-- Range-based update: replace a subarray
@[spec]
def Rust_primitives.Hax.Monomorphized_update_at.update_at_range {α n}
    (a : Vector α n) (range : Core_models.Ops.Range.Range usize) (vals : RustSlice α) :
    RustM (Vector α n) :=
  let start := range.start.toNat
  let stop := range._end.toNat
  if h : start ≤ stop ∧ stop ≤ n ∧ vals.size = stop - start then
    pure (Vector.ofFn (n := n) fun i =>
      if start ≤ i.val ∧ i.val < stop then
        vals.getD (i.val - start) (a[i])
      else a[i])
  else
    .fail .arrayOutOfBounds

-- copy_from_slice: copies data from src slice into dst slice
@[spec]
def Core_models.Slice.Impl.copy_from_slice (α : Type) (dst : RustSlice α)
    (src : RustSlice α) : RustM (RustSlice α) :=
  if dst.size = src.size then pure src
  else .fail .arrayOutOfBounds

end RustArray
