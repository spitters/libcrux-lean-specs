/-
# Libcrux-specific Impl Numbering Definitions

The hax extraction for the libcrux-specs crate uses Impl numbers that differ from
the hax prelude's `Core_models.Num` numbering (which represents the Rust std lib).

Extraction numbering (in `Libcrux_specs.Num` namespace):
  Impl_6 = u8, Impl_8 = u32, Impl_9 = u64, Impl_10 = u128

We provide concrete implementations for all methods the extraction references.
-/

import HaxPrelude

set_option linter.unusedVariables false

namespace Libcrux_specs.Num

/-! ## Impl_6: u8 methods -/
namespace Impl_6

@[simp, spec]
def leading_zeros (x : u8) : RustM u32 :=
  -- Count leading zeros by checking each bit position
  let n := x.toNat
  pure (UInt32.ofNat (
    if n ≥ 128 then 0
    else if n ≥ 64 then 1
    else if n ≥ 32 then 2
    else if n ≥ 16 then 3
    else if n ≥ 8 then 4
    else if n ≥ 4 then 5
    else if n ≥ 2 then 6
    else if n ≥ 1 then 7
    else 8))

end Impl_6

/-! ## Impl_8: u32 methods -/
namespace Impl_8

-- Delegate to prelude's Impl_8 (which IS u32 wrapping ops)
@[simp, spec]
def wrapping_add (x y : u32) : RustM u32 := Core_models.Num.Impl_8.wrapping_add x y

@[simp, spec]
def rotate_right (x : u32) (n : u32) : RustM u32 :=
  Core_models.Num.Impl_8.rotate_right x n.toNat

@[simp, spec]
def rotate_left (x : u32) (n : u32) : RustM u32 :=
  Core_models.Num.Impl_8.rotate_left x n.toNat

@[simp, spec]
def from_be_bytes (x : Vector u8 4) : RustM u32 := Core_models.Num.Impl_8.from_be_bytes x

@[simp, spec]
def to_be_bytes (x : u32) : RustM (Vector u8 4) := Core_models.Num.Impl_8.to_be_bytes x

@[simp, spec]
def from_le_bytes (x : Vector u8 4) : RustM u32 := pure (Core_models.Num.Impl_8.from_le_bytes x)

@[simp, spec]
def to_le_bytes (x : u32) : RustM (Vector u8 4) := Core_models.Num.Impl_8.to_le_bytes x

@[simp, spec]
def pow (base : u32) (exp : u32) : RustM u32 := Core_models.Num.Impl_8.pow base exp

end Impl_8

/-! ## Impl_9: u64 methods -/
namespace Impl_9

@[simp, spec]
def wrapping_add (x y : u64) : RustM u64 := pure (x + y)

@[simp, spec]
def wrapping_sub (x y : u64) : RustM u64 := pure (x - y)

@[simp, spec]
def wrapping_mul (x y : u64) : RustM u64 := pure (x * y)

@[simp, spec]
def wrapping_neg (x : u64) : RustM u64 := pure (0 - x)

@[simp, spec]
def rotate_right (x : u64) (n : u32) : RustM u64 :=
  pure (UInt64.ofBitVec (BitVec.rotateRight x.toBitVec n.toNat))

@[simp, spec]
def rotate_left (x : u64) (n : u32) : RustM u64 :=
  pure (UInt64.ofBitVec (BitVec.rotateLeft x.toBitVec n.toNat))

@[simp, spec]
def to_be_bytes (x : u64) : RustM (Vector u8 8) :=
  pure #v[
    (x >>> 56 % 256).toUInt8,
    (x >>> 48 % 256).toUInt8,
    (x >>> 40 % 256).toUInt8,
    (x >>> 32 % 256).toUInt8,
    (x >>> 24 % 256).toUInt8,
    (x >>> 16 % 256).toUInt8,
    (x >>> 8 % 256).toUInt8,
    (x % 256).toUInt8]

@[simp, spec]
def to_le_bytes (x : u64) : RustM (Vector u8 8) :=
  pure #v[
    (x % 256).toUInt8,
    (x >>> 8 % 256).toUInt8,
    (x >>> 16 % 256).toUInt8,
    (x >>> 24 % 256).toUInt8,
    (x >>> 32 % 256).toUInt8,
    (x >>> 40 % 256).toUInt8,
    (x >>> 48 % 256).toUInt8,
    (x >>> 56 % 256).toUInt8]

@[simp, spec]
def from_be_bytes (x : Vector u8 8) : RustM u64 :=
  pure (
    (x[0].toUInt64 <<< 56) +
    (x[1].toUInt64 <<< 48) +
    (x[2].toUInt64 <<< 40) +
    (x[3].toUInt64 <<< 32) +
    (x[4].toUInt64 <<< 24) +
    (x[5].toUInt64 <<< 16) +
    (x[6].toUInt64 <<< 8) +
    x[7].toUInt64)

@[simp, spec]
def from_le_bytes (x : Vector u8 8) : RustM u64 :=
  pure (
    x[0].toUInt64
    + (x[1].toUInt64 <<< 8)
    + (x[2].toUInt64 <<< 16)
    + (x[3].toUInt64 <<< 24)
    + (x[4].toUInt64 <<< 32)
    + (x[5].toUInt64 <<< 40)
    + (x[6].toUInt64 <<< 48)
    + (x[7].toUInt64 <<< 56))

@[simp, spec]
def overflowing_add (x y : u64) : RustM (u64 × Bool) :=
  let sum := x + y
  let carry := (x.toNat + y.toNat) ≥ 2^64
  pure (sum, carry)

@[simp, spec]
def overflowing_sub (x y : u64) : RustM (u64 × Bool) :=
  let diff := x - y
  let borrow := y.toNat > x.toNat
  pure (diff, borrow)

@[simp, spec]
def leading_zeros (x : u64) : RustM u32 :=
  -- Simple implementation: count leading zeros
  let n := x.toNat
  pure (UInt32.ofNat (
    if n ≥ 2^63 then 0
    else if n ≥ 2^62 then 1
    else if n ≥ 2^61 then 2
    else if n ≥ 2^60 then 3
    else if n ≥ 2^59 then 4
    else if n ≥ 2^58 then 5
    else if n ≥ 2^57 then 6
    else if n ≥ 2^56 then 7
    else if n ≥ 2^55 then 8
    else if n ≥ 2^54 then 9
    else if n ≥ 2^53 then 10
    else if n ≥ 2^52 then 11
    else if n ≥ 2^51 then 12
    else if n ≥ 2^50 then 13
    else if n ≥ 2^49 then 14
    else if n ≥ 2^48 then 15
    else if n ≥ 2^47 then 16
    else if n ≥ 2^46 then 17
    else if n ≥ 2^45 then 18
    else if n ≥ 2^44 then 19
    else if n ≥ 2^43 then 20
    else if n ≥ 2^42 then 21
    else if n ≥ 2^41 then 22
    else if n ≥ 2^40 then 23
    else if n ≥ 2^39 then 24
    else if n ≥ 2^38 then 25
    else if n ≥ 2^37 then 26
    else if n ≥ 2^36 then 27
    else if n ≥ 2^35 then 28
    else if n ≥ 2^34 then 29
    else if n ≥ 2^33 then 30
    else if n ≥ 2^32 then 31
    else if n ≥ 2^31 then 32
    else if n ≥ 2^30 then 33
    else if n ≥ 2^29 then 34
    else if n ≥ 2^28 then 35
    else if n ≥ 2^27 then 36
    else if n ≥ 2^26 then 37
    else if n ≥ 2^25 then 38
    else if n ≥ 2^24 then 39
    else if n ≥ 2^23 then 40
    else if n ≥ 2^22 then 41
    else if n ≥ 2^21 then 42
    else if n ≥ 2^20 then 43
    else if n ≥ 2^19 then 44
    else if n ≥ 2^18 then 45
    else if n ≥ 2^17 then 46
    else if n ≥ 2^16 then 47
    else if n ≥ 2^15 then 48
    else if n ≥ 2^14 then 49
    else if n ≥ 2^13 then 50
    else if n ≥ 2^12 then 51
    else if n ≥ 2^11 then 52
    else if n ≥ 2^10 then 53
    else if n ≥ 2^9 then 54
    else if n ≥ 2^8 then 55
    else if n ≥ 2^7 then 56
    else if n ≥ 2^6 then 57
    else if n ≥ 2^5 then 58
    else if n ≥ 2^4 then 59
    else if n ≥ 2^3 then 60
    else if n ≥ 2^2 then 61
    else if n ≥ 2^1 then 62
    else if n ≥ 1 then 63
    else 64))

end Impl_9

/-! ## Impl_10: u128 methods -/
namespace Impl_10

@[simp, spec]
def wrapping_add (x y : u128) : RustM u128 := pure (x + y)

@[simp, spec]
def wrapping_sub (x y : u128) : RustM u128 := pure (x - y)

@[simp, spec]
def wrapping_mul (x y : u128) : RustM u128 := pure (x * y)

@[simp, spec]
def wrapping_neg (x : u128) : RustM u128 := pure (0 - x)

/-- overflowing_add returns (result, carry_flag) -/
@[simp, spec]
def overflowing_add (x y : u128) : RustM (u128 × Bool) :=
  let sum := x + y
  let carry := (x.toNat + y.toNat) ≥ 2^128
  pure (sum, carry)

def MAX : u128 := BitVec.ofNat 128 (2^128 - 1)

def MIN : u128 := BitVec.ofNat 128 0

private def u128_getbyte (x : u128) (shift : Nat) : u8 :=
  UInt8.ofNat ((x >>> shift).toNat % 256)

@[simp, spec]
def to_be_bytes (x : u128) : RustM (Vector u8 16) :=
  pure #v[
    u128_getbyte x 120, u128_getbyte x 112, u128_getbyte x 104, u128_getbyte x 96,
    u128_getbyte x 88, u128_getbyte x 80, u128_getbyte x 72, u128_getbyte x 64,
    u128_getbyte x 56, u128_getbyte x 48, u128_getbyte x 40, u128_getbyte x 32,
    u128_getbyte x 24, u128_getbyte x 16, u128_getbyte x 8, u128_getbyte x 0]

@[simp, spec]
def to_le_bytes (x : u128) : RustM (Vector u8 16) :=
  pure #v[
    u128_getbyte x 0, u128_getbyte x 8, u128_getbyte x 16, u128_getbyte x 24,
    u128_getbyte x 32, u128_getbyte x 40, u128_getbyte x 48, u128_getbyte x 56,
    u128_getbyte x 64, u128_getbyte x 72, u128_getbyte x 80, u128_getbyte x 88,
    u128_getbyte x 96, u128_getbyte x 104, u128_getbyte x 112, u128_getbyte x 120]

end Impl_10

end Libcrux_specs.Num

/-!
## OrOp bridge for Shl.AssociatedTypes.Output

When the hax extraction generates `(x <<< y) ||| z`, the result type of `<<<` is
`Core_models.Ops.Bit.Shl.AssociatedTypes.Output α β`. Although this is `@[reducible]`
to `α`, typeclass resolution can fail to find `OrOp` when the LHS type contains
unresolved metavariables.

We add a forwarding instance that resolves `OrOp` on `Shl.AssociatedTypes.Output`.
-/

instance OrOp_Shl_Output {α β : Type}
    [inst : Core_models.Ops.Bit.Shl.AssociatedTypes α β]
    [OrOp inst.Output] :
    OrOp (Core_models.Ops.Bit.Shl.AssociatedTypes.Output α β) :=
  ‹OrOp inst.Output›

instance Complement_Shl_Output {α β : Type}
    [inst : Core_models.Ops.Bit.Shl.AssociatedTypes α β]
    [Complement inst.Output] :
    Complement (Core_models.Ops.Bit.Shl.AssociatedTypes.Output α β) :=
  ‹Complement inst.Output›

instance AndOp_Shl_Output {α β : Type}
    [inst : Core_models.Ops.Bit.Shl.AssociatedTypes α β]
    [AndOp inst.Output] :
    AndOp (Core_models.Ops.Bit.Shl.AssociatedTypes.Output α β) :=
  ‹AndOp inst.Output›

instance XorOp_Shl_Output {α β : Type}
    [inst : Core_models.Ops.Bit.Shl.AssociatedTypes α β]
    [XorOp inst.Output] :
    XorOp (Core_models.Ops.Bit.Shl.AssociatedTypes.Output α β) :=
  ‹XorOp inst.Output›

-- Also for Shr output
instance OrOp_Shr_Output {α β : Type}
    [inst : Core_models.Ops.Bit.Shr.AssociatedTypes α β]
    [OrOp inst.Output] :
    OrOp (Core_models.Ops.Bit.Shr.AssociatedTypes.Output α β) :=
  ‹OrOp inst.Output›

-- Concrete Add/Mul on Mul.Output and Shr.Output for u128 field arithmetic
-- (needed because hax extraction produces `(a *? b) +? c` where the result of `*?`
-- has type `Mul.AssociatedTypes.Output u128 u128` and Lean can't see through it)
instance : Core_models.Ops.Arith.Add.AssociatedTypes
    (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128) u128 where
  Output := u128
instance : Core_models.Ops.Arith.Add
    (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128) u128 where
  add x y := pure (x + y)
instance : Core_models.Ops.Arith.Add.AssociatedTypes
    (Core_models.Ops.Bit.Shr.AssociatedTypes.Output u128 i32) u128 where
  Output := u128
instance : Core_models.Ops.Arith.Add
    (Core_models.Ops.Bit.Shr.AssociatedTypes.Output u128 i32) u128 where
  add x y := pure (x + y)
instance : Cast (Core_models.Ops.Bit.Shr.AssociatedTypes.Output u128 i32) u64 where
  cast x := pure (UInt64.ofNat x.toNat)
instance : Core_models.Ops.Arith.Mul.AssociatedTypes
    (Core_models.Ops.Bit.Shr.AssociatedTypes.Output u128 i32) u64 where
  Output := u128
instance : Core_models.Ops.Arith.Mul
    (Core_models.Ops.Bit.Shr.AssociatedTypes.Output u128 i32) u64 where
  mul x y := pure (x * BitVec.ofNat 128 y.toNat)

-- Add on Mul.Output + Mul.Output (for schoolbook multiplication chains: (a*b) + (c*d))
instance : Core_models.Ops.Arith.Add.AssociatedTypes
    (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128)
    (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128) where
  Output := u128
instance : Core_models.Ops.Arith.Add
    (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128)
    (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128) where
  add x y := pure (x + y)

-- Add on Add.Output + Mul.Output (for chained: ((a*b)+(c*d)) + (e*f))
instance : Core_models.Ops.Arith.Add.AssociatedTypes
    (Core_models.Ops.Arith.Add.AssociatedTypes.Output
      (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128)
      (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128))
    (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128) where
  Output := u128
instance : Core_models.Ops.Arith.Add
    (Core_models.Ops.Arith.Add.AssociatedTypes.Output
      (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128)
      (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128))
    (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128) where
  add (x : u128) (y : u128) := pure (x + y)

-- Continue chain: (((a*b)+(c*d))+(e*f)) + (g*h)
instance : Core_models.Ops.Arith.Add.AssociatedTypes
    (Core_models.Ops.Arith.Add.AssociatedTypes.Output
      (Core_models.Ops.Arith.Add.AssociatedTypes.Output
        (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128)
        (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128))
      (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128))
    (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128) where
  Output := u128
instance : Core_models.Ops.Arith.Add
    (Core_models.Ops.Arith.Add.AssociatedTypes.Output
      (Core_models.Ops.Arith.Add.AssociatedTypes.Output
        (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128)
        (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128))
      (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128))
    (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128) where
  add (x : u128) (y : u128) := pure (x + y)

-- 4-deep chain: ((((a*b)+(c*d))+(e*f))+(g*h)) + (i*j)
instance : Core_models.Ops.Arith.Add.AssociatedTypes
    (Core_models.Ops.Arith.Add.AssociatedTypes.Output
      (Core_models.Ops.Arith.Add.AssociatedTypes.Output
        (Core_models.Ops.Arith.Add.AssociatedTypes.Output
          (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128)
          (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128))
        (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128))
      (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128))
    (Core_models.Ops.Arith.Mul.AssociatedTypes.Output u128 u128) where
  Output := u128
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

-- Generic forwarding instances for Mul.AssociatedTypes.Output (same pattern as Shl_Output)
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

-- Cast from Mul.Output
instance Cast_Mul_Output {α β γ : Type}
    [inst : Core_models.Ops.Arith.Mul.AssociatedTypes α β]
    [Cast inst.Output γ] :
    Cast (Core_models.Ops.Arith.Mul.AssociatedTypes.Output α β) γ :=
  ‹Cast inst.Output γ›

-- HAnd on Mul.Output
instance HAnd_Mul_Output {α β γ δ : Type}
    [inst : Core_models.Ops.Arith.Mul.AssociatedTypes α β]
    [HAnd inst.Output γ δ] :
    HAnd (Core_models.Ops.Arith.Mul.AssociatedTypes.Output α β) γ δ :=
  ‹HAnd inst.Output γ δ›

-- Add on Shr output (for carry + r patterns)
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

-- Cast from Shr.Output (for cast_op carry)
instance Cast_Shr_Output {α β γ : Type}
    [inst : Core_models.Ops.Bit.Shr.AssociatedTypes α β]
    [Cast inst.Output γ] :
    Cast (Core_models.Ops.Bit.Shr.AssociatedTypes.Output α β) γ :=
  ‹Cast inst.Output γ›

-- Mul on Shr output (for carry * 19 patterns)
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
## RangeTo support
-/

/-- RangeTo: `..end` (from start to end) -/
structure Core_models.Ops.Range.RangeTo (α : Type) where
  _end : α

/-!
## Misc missing identifiers
-/

/-- while_loop_return: like while_loop but the body returns ControlFlow.
    Break exits the loop early, Continue provides the next state.
    **Fuel-bounded** (10 000 iterations). See `while_loop'` for soundness caveat. -/
noncomputable def Rust_primitives.Hax.while_loop_return {β R : Type}
    (inv : β → RustM Prop)
    (cond : β → RustM Bool)
    (termination : β → RustM Hax_lib.Int.Int)
    (init : β)
    (body : β → RustM (Core_models.Ops.Control_flow.ControlFlow R β)) :
    RustM (Core_models.Ops.Control_flow.ControlFlow R β) := do
  let rec loop (fuel : Nat) (state : β) : RustM (Core_models.Ops.Control_flow.ControlFlow R β) :=
    match fuel with
    | 0 => pure (Core_models.Ops.Control_flow.ControlFlow.Continue state)
    | n + 1 => do
      let c ← cond state
      if c then
        match (← body state) with
        | Core_models.Ops.Control_flow.ControlFlow.Break r =>
          pure (Core_models.Ops.Control_flow.ControlFlow.Break r)
        | Core_models.Ops.Control_flow.ControlFlow.Continue next =>
          loop n next
      else
        pure (Core_models.Ops.Control_flow.ControlFlow.Continue state)
  loop 10000 init

/-- while_loop_cf: like while_loop but the body returns ControlFlow.
    On Break, extracts the continuation value. On Continue, provides next state.
    **Fuel-bounded** (10 000 iterations). See `while_loop'` for soundness caveat. -/
noncomputable def Rust_primitives.Hax.while_loop_cf {β : Type}
    (inv : β → RustM Prop)
    (cond : β → RustM Bool)
    (termination : β → RustM Hax_lib.Int.Int)
    (init : β)
    (body : β → RustM (Core_models.Ops.Control_flow.ControlFlow β β)) :
    RustM β := do
  let rec loop (fuel : Nat) (state : β) : RustM β :=
    match fuel with
    | 0 => pure state
    | n + 1 => do
      let c ← cond state
      if c then
        match (← body state) with
        | Core_models.Ops.Control_flow.ControlFlow.Break v => pure v
        | Core_models.Ops.Control_flow.ControlFlow.Continue next =>
          loop n next
      else
        pure state
  loop 10000 init

/-!
## Cast instances for u128 (BitVec 128)

The Cast macro in the hax prelude covers UInt8-UInt64, USize64, Int8-Int64, ISize,
but NOT u128 = BitVec 128. We add Cast instances for u128 ↔ all other types.
-/

@[spec] instance : Cast u8 u128 where cast x := pure (BitVec.ofNat 128 x.toNat)
@[spec] instance : Cast u16 u128 where cast x := pure (BitVec.ofNat 128 x.toNat)
@[spec] instance : Cast u32 u128 where cast x := pure (BitVec.ofNat 128 x.toNat)
@[spec] instance : Cast u64 u128 where cast x := pure (BitVec.ofNat 128 x.toNat)
@[spec] instance : Cast usize u128 where cast x := pure (BitVec.ofNat 128 x.toNat)
@[spec] instance : Cast u128 u8 where cast x := pure (UInt8.ofNat x.toNat)
@[spec] instance : Cast u128 u16 where cast x := pure (UInt16.ofNat x.toNat)
@[spec] instance : Cast u128 u32 where cast x := pure (UInt32.ofNat x.toNat)
@[spec] instance : Cast u128 u64 where cast x := pure (UInt64.ofNat x.toNat)
@[spec] instance : Cast u128 usize where cast x := pure (USize64.ofNat x.toNat)
@[spec] instance : Cast u128 u128 where cast x := pure x
@[spec] instance : Cast Bool u8 where cast b := pure (if b then 1 else 0)
@[spec] instance : Cast Bool u32 where cast b := pure (if b then 1 else 0)
@[spec] instance : Cast Bool u64 where cast b := pure (if b then 1 else 0)
@[spec] instance : Cast Bool u128 where cast b := pure (if b then 1 else 0)
@[spec] instance : Cast Bool usize where cast b := pure (if b then 1 else 0)

-- Cast from signed types to u128
@[spec] instance : Cast i32 u128 where cast x := pure (BitVec.ofNat 128 x.toNatClampNeg)
@[spec] instance : Cast i64 u128 where cast x := pure (BitVec.ofNat 128 x.toNatClampNeg)

/-!
## Fuel-based while_loop wrapper

The hax `while_loop` requires `pureInv`, `_pureTermination`, and `pureCond`
proof parameters that `mvcgen` can't synthesize for complex extracted loops.
We provide a fuel-based wrapper that avoids these proof obligations entirely.

### Soundness caveat

The fuel bound (100000) is **not** verified to be sufficient for all inputs.
If a loop exceeds the fuel budget, `while_loop_fuel` silently returns the
current intermediate state rather than signalling an error. This means:

1. Any theorem about the result of a fuel-bounded loop carries an implicit
   assumption that the loop terminated within the fuel budget.
2. For crypto spec loops on fixed-length (16/32-byte) inputs, the actual
   iteration counts are small (e.g. SHA-256: 64 rounds, AES: 10 rounds),
   so the 100 000 bound is conservative by orders of magnitude.
3. For variable-length inputs (not currently used), the fuel bound would
   need to be validated per-algorithm.

A proper fix would replace fuel with a termination proof or return
`Option β` on fuel exhaustion. This is tracked as future work.
-/

private def while_loop_fuel {β : Type}
    (cond : β → RustM Bool) (body : β → RustM β) : Nat → β → RustM β
  | 0, state => pure state
  | n + 1, state => do
    if (← cond state) then while_loop_fuel cond body n (← body state)
    else pure state

def Rust_primitives.Hax.while_loop' {β : Type}
    (_inv : β → RustM Prop)
    (cond : β → RustM Bool)
    (_termination : β → RustM Hax_lib.Int.Int)
    (init : β)
    (body : β → RustM β) : RustM β :=
  while_loop_fuel cond body 100000 init

/-!
## Slice split_at (not in prelude)
-/

def Core_models.Slice.Impl.split_at (T : Type) (s : RustSlice T) (mid : usize) :
    RustM (RustSlice T × RustSlice T) :=
  let n := mid.toNat
  if n ≤ s.size then pure (s.take n, s.drop n)
  else .fail .arrayOutOfBounds

/-!
## Additional Cast instances
-/

@[spec] instance : Cast Bool u16 where cast b := pure (if b then 1 else 0)
@[spec] instance : Cast u16 u8 where cast x := pure (UInt8.ofNat x.toNat)
@[spec] instance : Cast u32 u8 where cast x := pure (UInt8.ofNat x.toNat)

-- Cast i32→usize for shift amounts
@[spec] instance : Cast usize i32 where cast x := pure (Int32.ofNat x.toNat)

/-!
## Rev iterator adapter for RSA extraction
-/

namespace Core_models.Iter.Adapters.Rev
structure Rev (I : Type) where
  iter : I
end Core_models.Iter.Adapters.Rev

/-- Reverse a range iterator -/
def Core_models.Iter.Traits.Iterator.Iterator.rev
    (I : Type) (iter : I) : RustM (Core_models.Iter.Adapters.Rev.Rev I) :=
  pure ⟨iter⟩

/-- IteratorItems for Rev (Range usize) — produces items in reverse order -/
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

/-- IntoIterator for Rev (Range usize) — just return self -/
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
## Fmt.Rt panic helper
-/

noncomputable def Core_models.Panicking.panic_str {α : Type} (_msg : String) : RustM α := .fail .panic

