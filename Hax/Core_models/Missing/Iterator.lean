import Hax.Core_models.Extracted
import Hax.Rust_primitives.Tuple
import Hax.Rust_primitives.Num

/-!
# Iterator Infrastructure for Hax Extractions

Provides the Iterator types, adapter types, and operations needed by
hax-extracted Rust code that uses iterators (fold, enumerate, zip, map, collect).
-/

open Rust_primitives.Hax
open Core_models.Ops.Control_flow

set_option linter.unusedVariables false

/-! ## Iterator Concrete Types -/

structure Alloc.Vec.Into_iter.IntoIter (T : Type) (_A : Type) where
  data : Array T

structure Core_models.Slice.Iter.Iter (T : Type) where
  data : Array T

/-! ## Inclusive Range -/

structure Core_models.Ops.Range.RangeInclusive (T : Type) where
  start : T
  end_ : T

def Core_models.Ops.Range.Impl_7.new (_T : Type) (s e : _T) :
    RustM (Core_models.Ops.Range.RangeInclusive _T) :=
  pure ⟨s, e⟩

/-! ## Iterator Adapter Types -/

structure Core_models.Iter.Adapters.Enumerate.Enumerate (I : Type) where
  inner : I

structure Core_models.Iter.Adapters.Zip.Zip (I1 I2 : Type) where
  inner1 : I1
  inner2 : I2

/-! ## Map Adapter -/

class HasRustMOutput (F : Type) where
  Output : outParam Type

instance {α β : Type} : HasRustMOutput (α → RustM β) where
  Output := β

structure Core_models.Iter.Adapters.Map.Map (I : Type) (F : Type)
    [HasRustMOutput F] where
  data : Array (HasRustMOutput.Output F)

/-! ## IteratorItems Typeclass -/

class IteratorItems (I : Type) where
  Item : outParam Type
  toArrayM : I → RustM (Array Item)

attribute [reducible] IteratorItems.Item

instance {T A : Type} : IteratorItems (Alloc.Vec.Into_iter.IntoIter T A) where
  Item := T
  toArrayM iter := pure iter.data

instance {T : Type} : IteratorItems (Core_models.Slice.Iter.Iter T) where
  Item := T
  toArrayM iter := pure iter.data

instance {T : Type} : IteratorItems (Array T) where
  Item := T
  toArrayM a := pure a

instance : IteratorItems (Core_models.Ops.Range.RangeInclusive USize64) where
  Item := USize64
  toArrayM r := pure <| Id.run do
    let s := r.start.toNat
    let e := r.end_.toNat
    let mut result : Array USize64 := Array.mkEmpty (e - s + 1)
    for i in [s : e + 1] do
      result := result.push (USize64.ofNat i)
    result

instance {I : Type} [IteratorItems I] :
    IteratorItems (Core_models.Iter.Adapters.Enumerate.Enumerate I) where
  Item := USize64 × IteratorItems.Item I
  toArrayM e := do
    let items ← IteratorItems.toArrayM e.inner
    let mut result : Array (USize64 × IteratorItems.Item I) :=
      Array.mkEmpty items.size
    for h : i in [:items.size] do
      result := result.push (USize64.ofNat i, items[i])
    pure result

instance {I1 I2 : Type} [inst1 : IteratorItems I1] [inst2 : IteratorItems I2] :
    IteratorItems (Core_models.Iter.Adapters.Zip.Zip I1 I2) where
  Item := inst1.Item × inst2.Item
  toArrayM z := do
    let a1 ← IteratorItems.toArrayM z.inner1
    let a2 ← IteratorItems.toArrayM z.inner2
    let n := min a1.size a2.size
    pure <| Array.ofFn (n := n) fun ⟨i, hi⟩ =>
      (a1[i]'(Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)),
       a2[i]'(Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _)))

instance {I F : Type} [HasRustMOutput F] :
    IteratorItems (Core_models.Iter.Adapters.Map.Map I F) where
  Item := HasRustMOutput.Output F
  toArrayM m := pure m.data

/-! ## IntoIterator Instances

`into_iter` has type:
  `(Self : Type) → [AssocTypes Self] → [IntoIterator Self] → Self → RustM IntoIter`
So instances provide: `into_iter := fun v => pure ...`
-/

open Core_models.Iter.Traits.Collect in
@[reducible]
instance {T A : Type} : IntoIterator.AssociatedTypes (Alloc.Vec.Vec T A) where
  IntoIter := Alloc.Vec.Into_iter.IntoIter T A

open Core_models.Iter.Traits.Collect in
instance {T A : Type} : IntoIterator (Alloc.Vec.Vec T A) where
  into_iter := fun v => pure ⟨v⟩

open Core_models.Iter.Traits.Collect in
@[reducible]
instance {T : Type} : IntoIterator.AssociatedTypes (RustSlice T) where
  IntoIter := Array T

open Core_models.Iter.Traits.Collect in
instance {T : Type} : IntoIterator (RustSlice T) where
  into_iter := fun v => pure v

open Core_models.Iter.Traits.Collect in
@[reducible]
instance : IntoIterator.AssociatedTypes
    (Core_models.Ops.Range.RangeInclusive USize64) where
  IntoIter := Array USize64

open Core_models.Iter.Traits.Collect in
instance : IntoIterator (Core_models.Ops.Range.RangeInclusive USize64) where
  into_iter := fun r => pure <| Id.run do
    let s := r.start.toNat
    let e := r.end_.toNat
    let mut result : Array USize64 := Array.mkEmpty (e - s + 1)
    for i in [s : e + 1] do
      result := result.push (USize64.ofNat i)
    result

open Core_models.Iter.Traits.Collect in
@[reducible]
instance {I : Type} :
    IntoIterator.AssociatedTypes
      (Core_models.Iter.Adapters.Enumerate.Enumerate I) where
  IntoIter := Core_models.Iter.Adapters.Enumerate.Enumerate I

open Core_models.Iter.Traits.Collect in
instance {I : Type} :
    IntoIterator (Core_models.Iter.Adapters.Enumerate.Enumerate I) where
  into_iter := fun e => pure e

open Core_models.Iter.Traits.Collect in
@[reducible]
instance {I1 I2 : Type} :
    IntoIterator.AssociatedTypes
      (Core_models.Iter.Adapters.Zip.Zip I1 I2) where
  IntoIter := Core_models.Iter.Adapters.Zip.Zip I1 I2

open Core_models.Iter.Traits.Collect in
instance {I1 I2 : Type} :
    IntoIterator (Core_models.Iter.Adapters.Zip.Zip I1 I2) where
  into_iter := fun z => pure z

open Core_models.Iter.Traits.Collect in
@[reducible]
instance {I F : Type} [HasRustMOutput F] :
    IntoIterator.AssociatedTypes
      (Core_models.Iter.Adapters.Map.Map I F) where
  IntoIter := Core_models.Iter.Adapters.Map.Map I F

open Core_models.Iter.Traits.Collect in
instance {I F : Type} [HasRustMOutput F] :
    IntoIterator (Core_models.Iter.Adapters.Map.Map I F) where
  into_iter := fun m => pure m

/-! ## Iterator Operations -/

namespace Core_models.Iter.Traits.Iterator.Iterator

def fold {I : Type} [IteratorItems I] {B : Type}
    (iter : I) (init : B) (f : B → IteratorItems.Item I → RustM B) : RustM B := do
  let items ← IteratorItems.toArrayM iter
  let mut acc := init
  for h : i in [:items.size] do
    acc ← f acc items[i]
  pure acc

def enumerate (I : Type) [IteratorItems I]
    (iter : I) :
    RustM (Core_models.Iter.Adapters.Enumerate.Enumerate I) :=
  pure ⟨iter⟩

def zip (I1 I2 : Type) [IteratorItems I1] [IteratorItems I2]
    (iter1 : I1) (iter2 : I2) :
    RustM (Core_models.Iter.Adapters.Zip.Zip I1 I2) :=
  pure ⟨iter1, iter2⟩

def map (I : Type) (_Out : Type) (F : Type) [IteratorItems I] [inst : HasRustMOutput F]
    (iter : I) (f : IteratorItems.Item I → RustM inst.Output) :
    RustM (Core_models.Iter.Adapters.Map.Map I F) := do
  let items ← IteratorItems.toArrayM iter
  let results ← items.mapM f
  pure ⟨results⟩

def collect (_I : Type) (_C : Type) [inst : IteratorItems _I]
    (iter : _I) : RustM (Array inst.Item) :=
  IteratorItems.toArrayM iter

end Core_models.Iter.Traits.Iterator.Iterator

/-! ## Slice Operations -/

def Core_models.Slice.Impl.iter (T : Type) (s : RustSlice T) :
    RustM (Core_models.Slice.Iter.Iter T) :=
  pure ⟨s⟩

/-! ## fold_return for Iterators -/

def Rust_primitives.Hax.Folds.fold_return {I : Type} [IteratorItems I]
    (iter : I) {α_acc α_ret : Type} (init : α_acc)
    (body : α_acc → IteratorItems.Item I →
      RustM (ControlFlow (ControlFlow α_ret (Tuple2 Tuple0 α_acc)) α_acc))
    : RustM (ControlFlow α_ret α_acc) := do
  let items ← IteratorItems.toArrayM iter
  let mut acc := init
  for h : i in [:items.size] do
    match ← body acc items[i] with
    | .Break (.Break res) => return .Break res
    | .Break (.Continue ⟨_, acc'⟩) => return .Continue acc'
    | .Continue acc' => acc := acc'
  pure (.Continue acc)
