import Hax.Core_models.Extracted
import Hax.Rust_primitives.Array

/-!
# Missing comparison and bitwise operations for hax extractions

Provides:
- `PartialEq` instance for `Vector α n` (RustArray)
- `PartialEq.ne` function (not a default trait method, but used by hax)
- `Ops.Bit.Not` class and Bool instance
- `Array.Impl_23.as_slice` (array-to-slice conversion)
-/

set_option linter.unusedVariables false

/-! ## PartialEq for Vector (RustArray) -/

open Core_models.Cmp in
@[reducible]
instance {α n} [BEq α] : PartialEq.AssociatedTypes (Vector α n) (Vector α n) where

open Core_models.Cmp in
instance {α n} [BEq α] : PartialEq (Vector α n) (Vector α n) where
  eq := fun self other => pure (self == other)

/-- `PartialEq::ne` — not a default method in hax's PartialEq class, defined as
    standalone function. -/
def Core_models.Cmp.PartialEq.ne (Self Rhs : Type)
    [Core_models.Cmp.PartialEq.AssociatedTypes Self Rhs]
    [Core_models.Cmp.PartialEq Self Rhs]
    (x : Self) (y : Rhs) : RustM Bool := do
  let eq_result ← Core_models.Cmp.PartialEq.eq Self Rhs x y
  pure (!eq_result)

/-! ## Bitwise Not -/

namespace Core_models.Ops.Bit

class Not.AssociatedTypes (Self : Type) where
  Output : Type

attribute [reducible] Not.AssociatedTypes.Output

class Not (Self : Type)
  [associatedTypes : outParam (Not.AssociatedTypes Self)]
  where
  not : Self → RustM associatedTypes.Output

@[reducible]
instance : Not.AssociatedTypes Bool where
  Output := Bool

instance : Not Bool where
  not b := pure (!b)

end Core_models.Ops.Bit

/-! ## Array as_slice -/

/-- Convert a fixed-size array (Vector) to a slice (Array). -/
def Core_models.Array.Impl_23.as_slice {T : Type} {n : Nat}
    (a : Vector T n) : RustM (RustSlice T) :=
  pure a.toArray
