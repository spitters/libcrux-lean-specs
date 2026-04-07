/-
# Cast instances for types not covered by the hax prelude

The hax prelude's Cast macro covers UInt8–UInt64, USize64, Int8–Int64, ISize,
but NOT u128 = BitVec 128 or Bool-to-integer casts. We add them here.
-/

import HaxPrelude

set_option autoImplicit false

/-! ## u128 ↔ all types -/

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

/-! ## Bool → integer types -/

@[spec] instance : Cast Bool u8 where cast b := pure (if b then 1 else 0)
@[spec] instance : Cast Bool u16 where cast b := pure (if b then 1 else 0)
@[spec] instance : Cast Bool u32 where cast b := pure (if b then 1 else 0)
@[spec] instance : Cast Bool u64 where cast b := pure (if b then 1 else 0)
@[spec] instance : Cast Bool u128 where cast b := pure (if b then 1 else 0)
@[spec] instance : Cast Bool usize where cast b := pure (if b then 1 else 0)

/-! ## Signed → u128 -/

@[spec] instance : Cast i32 u128 where cast x := pure (BitVec.ofNat 128 x.toNatClampNeg)
@[spec] instance : Cast i64 u128 where cast x := pure (BitVec.ofNat 128 x.toNatClampNeg)

/-! ## Cross-width unsigned truncation -/

@[spec] instance : Cast u16 u8 where cast x := pure (UInt8.ofNat x.toNat)
@[spec] instance : Cast u32 u8 where cast x := pure (UInt8.ofNat x.toNat)

/-! ## usize ↔ i32 (shift amounts) -/

@[spec] instance : Cast usize i32 where cast x := pure (Int32.ofNat x.toNat)
