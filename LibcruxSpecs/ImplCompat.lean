/-
# Typeclass forwarding instances and misc extraction compat

This file contains:
1. Forwarding instances for Shl/Shr/Mul/Add AssociatedTypes.Output
   (should be upstreamed to Cryspen's hax prelude)
2. Concrete u128 chain instances for schoolbook multiplication
3. RangeTo, split_at, Rev iterator, PartialEq Ordering, panic_str
-/

import HaxPrelude
import LibcruxSpecs.CastCompat

set_option linter.unusedVariables false
set_option autoImplicit false

/-!
## Forwarding instances for Shl/Shr.AssociatedTypes.Output

When hax generates `(x <<< y) ||| z`, the result type of `<<<` is
`Shl.AssociatedTypes.Output α β` which is `@[reducible]` to `α`, but
typeclass resolution can fail to find `OrOp` etc. on the wrapper type.
-/

instance OrOp_Shl_Output {α β : Type}
    [inst : Core_models.Ops.Bit.Shl.AssociatedTypes α β] [OrOp inst.Output] :
    OrOp (Core_models.Ops.Bit.Shl.AssociatedTypes.Output α β) := ‹OrOp inst.Output›

instance Complement_Shl_Output {α β : Type}
    [inst : Core_models.Ops.Bit.Shl.AssociatedTypes α β] [Complement inst.Output] :
    Complement (Core_models.Ops.Bit.Shl.AssociatedTypes.Output α β) := ‹Complement inst.Output›

instance AndOp_Shl_Output {α β : Type}
    [inst : Core_models.Ops.Bit.Shl.AssociatedTypes α β] [AndOp inst.Output] :
    AndOp (Core_models.Ops.Bit.Shl.AssociatedTypes.Output α β) := ‹AndOp inst.Output›

instance XorOp_Shl_Output {α β : Type}
    [inst : Core_models.Ops.Bit.Shl.AssociatedTypes α β] [XorOp inst.Output] :
    XorOp (Core_models.Ops.Bit.Shl.AssociatedTypes.Output α β) := ‹XorOp inst.Output›

instance OrOp_Shr_Output {α β : Type}
    [inst : Core_models.Ops.Bit.Shr.AssociatedTypes α β] [OrOp inst.Output] :
    OrOp (Core_models.Ops.Bit.Shr.AssociatedTypes.Output α β) := ‹OrOp inst.Output›

/-!
## Forwarding instances for Mul/Add/Shr AssociatedTypes.Output

Needed for u128 field arithmetic: hax produces `(a *? b) +? c` where `*?`
returns `Mul.AssociatedTypes.Output u128 u128` and `+?` needs `Add` on it.
-/

-- Generic forwarding: Mul.Output
instance Add_Mul_Output {α β γ : Type}
    [inst : Core_models.Ops.Arith.Mul.AssociatedTypes α β]
    [Core_models.Ops.Arith.Add.AssociatedTypes inst.Output γ]
    [Core_models.Ops.Arith.Add inst.Output γ] :
    Core_models.Ops.Arith.Add (Core_models.Ops.Arith.Mul.AssociatedTypes.Output α β) γ :=
  ‹Core_models.Ops.Arith.Add inst.Output γ›

instance Add_AssocTypes_Mul_Output {α β γ : Type}
    [inst : Core_models.Ops.Arith.Mul.AssociatedTypes α β]
    [Core_models.Ops.Arith.Add.AssociatedTypes inst.Output γ] :
    Core_models.Ops.Arith.Add.AssociatedTypes (Core_models.Ops.Arith.Mul.AssociatedTypes.Output α β) γ :=
  ‹Core_models.Ops.Arith.Add.AssociatedTypes inst.Output γ›

instance Cast_Mul_Output {α β γ : Type}
    [inst : Core_models.Ops.Arith.Mul.AssociatedTypes α β] [Cast inst.Output γ] :
    Cast (Core_models.Ops.Arith.Mul.AssociatedTypes.Output α β) γ := ‹Cast inst.Output γ›

instance HAnd_Mul_Output {α β γ δ : Type}
    [inst : Core_models.Ops.Arith.Mul.AssociatedTypes α β] [HAnd inst.Output γ δ] :
    HAnd (Core_models.Ops.Arith.Mul.AssociatedTypes.Output α β) γ δ := ‹HAnd inst.Output γ δ›

-- Generic forwarding: Shr.Output
instance Add_Shr_Output {α β γ : Type}
    [inst : Core_models.Ops.Bit.Shr.AssociatedTypes α β]
    [Core_models.Ops.Arith.Add.AssociatedTypes inst.Output γ]
    [Core_models.Ops.Arith.Add inst.Output γ] :
    Core_models.Ops.Arith.Add (Core_models.Ops.Bit.Shr.AssociatedTypes.Output α β) γ :=
  ‹Core_models.Ops.Arith.Add inst.Output γ›

instance Add_AssocTypes_Shr_Output {α β γ : Type}
    [inst : Core_models.Ops.Bit.Shr.AssociatedTypes α β]
    [Core_models.Ops.Arith.Add.AssociatedTypes inst.Output γ] :
    Core_models.Ops.Arith.Add.AssociatedTypes (Core_models.Ops.Bit.Shr.AssociatedTypes.Output α β) γ :=
  ‹Core_models.Ops.Arith.Add.AssociatedTypes inst.Output γ›

instance Cast_Shr_Output {α β γ : Type}
    [inst : Core_models.Ops.Bit.Shr.AssociatedTypes α β] [Cast inst.Output γ] :
    Cast (Core_models.Ops.Bit.Shr.AssociatedTypes.Output α β) γ := ‹Cast inst.Output γ›

instance Mul_Shr_Output {α β γ : Type}
    [inst : Core_models.Ops.Bit.Shr.AssociatedTypes α β]
    [Core_models.Ops.Arith.Mul.AssociatedTypes inst.Output γ]
    [Core_models.Ops.Arith.Mul inst.Output γ] :
    Core_models.Ops.Arith.Mul (Core_models.Ops.Bit.Shr.AssociatedTypes.Output α β) γ :=
  ‹Core_models.Ops.Arith.Mul inst.Output γ›

instance Mul_AssocTypes_Shr_Output {α β γ : Type}
    [inst : Core_models.Ops.Bit.Shr.AssociatedTypes α β]
    [Core_models.Ops.Arith.Mul.AssociatedTypes inst.Output γ] :
    Core_models.Ops.Arith.Mul.AssociatedTypes (Core_models.Ops.Bit.Shr.AssociatedTypes.Output α β) γ :=
  ‹Core_models.Ops.Arith.Mul.AssociatedTypes inst.Output γ›

/-!
## Concrete u128 chain instances for Curve25519 schoolbook multiplication

`fe_mul` computes `(a0*b0) +? (a1*b4_19) +? (a2*b3_19) +? ...` where each `+?`
chains through nested `Add.AssociatedTypes.Output` wrappers. Lean's typeclass
resolution can't see through chains deeper than 1, so we provide concrete
instances for chains up to depth 4 (the maximum in fe_mul's r0..r4).
-/

-- Concrete: Shr u128 i32 output ops (for carry propagation)
instance : Core_models.Ops.Arith.Add.AssociatedTypes
    (Core_models.Ops.Bit.Shr.AssociatedTypes.Output u128 i32) u128 where Output := u128
instance : Core_models.Ops.Arith.Add
    (Core_models.Ops.Bit.Shr.AssociatedTypes.Output u128 i32) u128 where add x y := pure (x + y)
instance : Cast (Core_models.Ops.Bit.Shr.AssociatedTypes.Output u128 i32) u64 where
  cast x := pure (UInt64.ofNat x.toNat)
instance : Core_models.Ops.Arith.Mul.AssociatedTypes
    (Core_models.Ops.Bit.Shr.AssociatedTypes.Output u128 i32) u64 where Output := u128
instance : Core_models.Ops.Arith.Mul
    (Core_models.Ops.Bit.Shr.AssociatedTypes.Output u128 i32) u64 where
  mul x y := pure (x * BitVec.ofNat 128 y.toNat)

-- Concrete: Mul u128 u128 output + u128
instance : Core_models.Ops.Arith.Add.AssociatedTypes
    (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128) u128 where Output := u128
instance : Core_models.Ops.Arith.Add
    (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128) u128 where add x y := pure (x + y)

-- Concrete: Mul.Output + Mul.Output (depth 1)
instance : Core_models.Ops.Arith.Add.AssociatedTypes
    (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128)
    (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128) where Output := u128
instance : Core_models.Ops.Arith.Add
    (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128)
    (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128) where add x y := pure (x + y)

-- Depth 2: ((a*b)+(c*d)) + (e*f)
instance : Core_models.Ops.Arith.Add.AssociatedTypes
    (Core_models.Ops.Arith.Add.AssociatedTypes.Output
      (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128)
      (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128))
    (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128) where Output := u128
instance : Core_models.Ops.Arith.Add
    (Core_models.Ops.Arith.Add.AssociatedTypes.Output
      (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128)
      (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128))
    (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128) where
  add (x : u128) (y : u128) := pure (x + y)

-- Depth 3: (((a*b)+(c*d))+(e*f)) + (g*h)
instance : Core_models.Ops.Arith.Add.AssociatedTypes
    (Core_models.Ops.Arith.Add.AssociatedTypes.Output
      (Core_models.Ops.Arith.Add.AssociatedTypes.Output
        (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128)
        (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128))
      (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128))
    (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128) where Output := u128
instance : Core_models.Ops.Arith.Add
    (Core_models.Ops.Arith.Add.AssociatedTypes.Output
      (Core_models.Ops.Arith.Add.AssociatedTypes.Output
        (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128)
        (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128))
      (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128))
    (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128) where
  add (x : u128) (y : u128) := pure (x + y)

-- Depth 4: ((((a*b)+(c*d))+(e*f))+(g*h)) + (i*j)
instance : Core_models.Ops.Arith.Add.AssociatedTypes
    (Core_models.Ops.Arith.Add.AssociatedTypes.Output
      (Core_models.Ops.Arith.Add.AssociatedTypes.Output
        (Core_models.Ops.Arith.Add.AssociatedTypes.Output
          (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128)
          (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128))
        (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128))
      (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128))
    (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128) where Output := u128
instance : Core_models.Ops.Arith.Add
    (Core_models.Ops.Arith.Add.AssociatedTypes.Output
      (Core_models.Ops.Arith.Add.AssociatedTypes.Output
        (Core_models.Ops.Arith.Add.AssociatedTypes.Output
          (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128)
          (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128))
        (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128))
      (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128))
    (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128) where
  add (x : u128) (y : u128) := pure (x + y)

/-!
## RangeTo support
-/

structure Core_models.Ops.Range.RangeTo (α : Type) where
  _end : α

/-!
## Slice split_at (not in prelude)
-/

def Core_models.Slice.Impl.split_at (T : Type) (s : RustSlice T) (mid : usize) :
    RustM (RustSlice T × RustSlice T) :=
  let n := mid.toNat
  if n ≤ s.size then pure (s.take n, s.drop n)
  else .fail .arrayOutOfBounds

/-!
## Rev iterator adapter (for RSA extraction)
-/

namespace Core_models.Iter.Adapters.Rev
structure Rev (I : Type) where
  iter : I
end Core_models.Iter.Adapters.Rev

def Core_models.Iter.Traits.Iterator.Iterator.rev
    (I : Type) (iter : I) : RustM (Core_models.Iter.Adapters.Rev.Rev I) :=
  pure ⟨iter⟩

instance : IteratorItems (Core_models.Iter.Adapters.Rev.Rev (Core_models.Ops.Range.Range USize64)) where
  Item := USize64
  toArrayM r := pure <| Id.run do
    let range := r.iter
    let s := range.start.toNat
    let e := range._end.toNat
    let mut result : Array USize64 := Array.mkEmpty (e - s)
    for i in List.range (e - s) do
      result := result.push (USize64.ofNat (e - 1 - i))
    result

@[reducible]
instance : Core_models.Iter.Traits.Collect.IntoIterator.AssociatedTypes
    (Core_models.Iter.Adapters.Rev.Rev (Core_models.Ops.Range.Range USize64)) where
  IntoIter := Core_models.Iter.Adapters.Rev.Rev (Core_models.Ops.Range.Range USize64)

instance : Core_models.Iter.Traits.Collect.IntoIterator
    (Core_models.Iter.Adapters.Rev.Rev (Core_models.Ops.Range.Range USize64)) where
  into_iter r := pure r

/-!
## PartialEq for Ordering (RSA comparison)
-/

namespace Core_models.Cmp
instance : BEq Core_models.Cmp.Ordering where
  beq a b := match a, b with
    | .Less, .Less => true
    | .Equal, .Equal => true
    | .Greater, .Greater => true
    | _, _ => false

instance : Core_models.Cmp.PartialEq.AssociatedTypes Core_models.Cmp.Ordering Core_models.Cmp.Ordering where
instance : Core_models.Cmp.PartialEq Core_models.Cmp.Ordering Core_models.Cmp.Ordering where
  eq a b := pure (a == b)
end Core_models.Cmp

/-!
## Panic helper
-/

noncomputable def Core_models.Panicking.panic_str {α : Type} (_msg : String) : RustM α := .fail .panic
