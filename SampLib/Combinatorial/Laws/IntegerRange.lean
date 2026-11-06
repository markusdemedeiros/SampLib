module

public import Mathlib.Data.Int.Basic

@[expose] public section

/-! # Consecutive integer lists -/

namespace SampLib.IntegerRange

/-- The list `lo, lo + 1, …, lo + n - 1`. -/
def interval (lo : ℤ) : ℕ → List ℤ
  | 0 => []
  | n + 1 => lo :: interval (lo + 1) n

end SampLib.IntegerRange
