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
set_option autoImplicit false

namespace Libcrux_specs.Num

/-! ## Impl_6: u8 methods -/
namespace Impl_6

@[simp, spec]
def leading_zeros (x : u8) : RustM u32 :=
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
    (x >>> 56 % 256).toUInt8, (x >>> 48 % 256).toUInt8,
    (x >>> 40 % 256).toUInt8, (x >>> 32 % 256).toUInt8,
    (x >>> 24 % 256).toUInt8, (x >>> 16 % 256).toUInt8,
    (x >>> 8 % 256).toUInt8, (x % 256).toUInt8]

@[simp, spec]
def to_le_bytes (x : u64) : RustM (Vector u8 8) :=
  pure #v[
    (x % 256).toUInt8, (x >>> 8 % 256).toUInt8,
    (x >>> 16 % 256).toUInt8, (x >>> 24 % 256).toUInt8,
    (x >>> 32 % 256).toUInt8, (x >>> 40 % 256).toUInt8,
    (x >>> 48 % 256).toUInt8, (x >>> 56 % 256).toUInt8]

@[simp, spec]
def from_be_bytes (x : Vector u8 8) : RustM u64 :=
  pure (
    (x[0].toUInt64 <<< 56) + (x[1].toUInt64 <<< 48) +
    (x[2].toUInt64 <<< 40) + (x[3].toUInt64 <<< 32) +
    (x[4].toUInt64 <<< 24) + (x[5].toUInt64 <<< 16) +
    (x[6].toUInt64 <<< 8) + x[7].toUInt64)

@[simp, spec]
def from_le_bytes (x : Vector u8 8) : RustM u64 :=
  pure (
    x[0].toUInt64 + (x[1].toUInt64 <<< 8) +
    (x[2].toUInt64 <<< 16) + (x[3].toUInt64 <<< 24) +
    (x[4].toUInt64 <<< 32) + (x[5].toUInt64 <<< 40) +
    (x[6].toUInt64 <<< 48) + (x[7].toUInt64 <<< 56))

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
  let n := x.toNat
  pure (UInt32.ofNat (
    if n ≥ 2^63 then 0 else if n ≥ 2^62 then 1 else if n ≥ 2^61 then 2
    else if n ≥ 2^60 then 3 else if n ≥ 2^59 then 4 else if n ≥ 2^58 then 5
    else if n ≥ 2^57 then 6 else if n ≥ 2^56 then 7 else if n ≥ 2^55 then 8
    else if n ≥ 2^54 then 9 else if n ≥ 2^53 then 10 else if n ≥ 2^52 then 11
    else if n ≥ 2^51 then 12 else if n ≥ 2^50 then 13 else if n ≥ 2^49 then 14
    else if n ≥ 2^48 then 15 else if n ≥ 2^47 then 16 else if n ≥ 2^46 then 17
    else if n ≥ 2^45 then 18 else if n ≥ 2^44 then 19 else if n ≥ 2^43 then 20
    else if n ≥ 2^42 then 21 else if n ≥ 2^41 then 22 else if n ≥ 2^40 then 23
    else if n ≥ 2^39 then 24 else if n ≥ 2^38 then 25 else if n ≥ 2^37 then 26
    else if n ≥ 2^36 then 27 else if n ≥ 2^35 then 28 else if n ≥ 2^34 then 29
    else if n ≥ 2^33 then 30 else if n ≥ 2^32 then 31 else if n ≥ 2^31 then 32
    else if n ≥ 2^30 then 33 else if n ≥ 2^29 then 34 else if n ≥ 2^28 then 35
    else if n ≥ 2^27 then 36 else if n ≥ 2^26 then 37 else if n ≥ 2^25 then 38
    else if n ≥ 2^24 then 39 else if n ≥ 2^23 then 40 else if n ≥ 2^22 then 41
    else if n ≥ 2^21 then 42 else if n ≥ 2^20 then 43 else if n ≥ 2^19 then 44
    else if n ≥ 2^18 then 45 else if n ≥ 2^17 then 46 else if n ≥ 2^16 then 47
    else if n ≥ 2^15 then 48 else if n ≥ 2^14 then 49 else if n ≥ 2^13 then 50
    else if n ≥ 2^12 then 51 else if n ≥ 2^11 then 52 else if n ≥ 2^10 then 53
    else if n ≥ 2^9 then 54 else if n ≥ 2^8 then 55 else if n ≥ 2^7 then 56
    else if n ≥ 2^6 then 57 else if n ≥ 2^5 then 58 else if n ≥ 2^4 then 59
    else if n ≥ 2^3 then 60 else if n ≥ 2^2 then 61 else if n ≥ 2^1 then 62
    else if n ≥ 1 then 63 else 64))

end Impl_9

/-! ## Impl_10: u128 methods -/
namespace Impl_10

@[simp, spec] def wrapping_add (x y : u128) : RustM u128 := pure (x + y)
@[simp, spec] def wrapping_sub (x y : u128) : RustM u128 := pure (x - y)
@[simp, spec] def wrapping_mul (x y : u128) : RustM u128 := pure (x * y)
@[simp, spec] def wrapping_neg (x : u128) : RustM u128 := pure (0 - x)

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
