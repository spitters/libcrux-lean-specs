/-
# Libcrux-specific Impl Numbering Definitions

The hax extraction for the libcrux-specs crate uses Impl numbers that differ from
the hax prelude's `Core_models.Num` numbering (which represents the Rust std lib).

Extraction numbering (in `Libcrux_specs.Num` namespace):
  Impl_6 = u8, Impl_8 = u32, Impl_9 = u64, Impl_10 = u128

We provide concrete implementations for all methods the extraction references.
-/

import Hax

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

/-!
## RangeTo support
-/

/-- RangeTo: `..end` (from start to end) -/
structure Core_models.Ops.Range.RangeTo (α : Type) where
  _end : α

/-!
## Misc missing identifiers
-/

/-- while_loop_return is used by hax for while loop early returns -/
def Rust_primitives.Hax.while_loop_return {α : Type} (x : α) : RustM α := pure x

