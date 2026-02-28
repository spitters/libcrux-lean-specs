

/-

# Ranges

-/

/-- Type of ranges -/
structure Core_models.Ops.Range.Range (α: Type) where
  start : α
  _end : α

/-- RangeFrom: `start..` (from start to end) -/
structure Core_models.Ops.Range.RangeFrom (α : Type) where
  start : α
