module

public import Mathlib.Data.Nat.Log
public import Mathlib.Order.MinMax

@[expose] public section

/-! # Finite logarithmic magnitude buckets -/

namespace SampLib.LogUniform

/-- Last nonempty magnitude bucket below an inclusive bound. -/
def lastLevel (maximum base : ℕ) : ℕ := Nat.clog base (maximum + 1)

/-- Positive levels have exponentially spaced lower endpoints. -/
def lower (maximum base level : ℕ) : ℕ := min maximum (base ^ (level - 1))

/-- The last bucket may be truncated by the inclusive bound. -/
def upper (maximum base level : ℕ) : ℕ := min maximum (base ^ level - 1)

@[simp] theorem lastLevel_zero (base : ℕ) : lastLevel 0 base = 0 := by
  simp [lastLevel]

/-- Every positive magnitude bucket is a valid inclusive interval. -/
theorem lower_le_upper (maximum base level : ℕ) (hb : 1 < base) (hl : 0 < level) :
    lower maximum base level ≤ upper maximum base level := by
  unfold lower upper
  apply min_le_min_left maximum
  have h := Nat.pow_lt_pow_right hb (show level - 1 < level by omega)
  omega

/-- Positive sampled levels begin no later than the upper bound. -/
theorem lower_pow_le (maximum base level : ℕ) (hl : 0 < level)
    (hlevel : level ≤ lastLevel maximum base) : base ^ (level - 1) ≤ maximum := by
  have hlt : level - 1 < Nat.clog base (maximum + 1) := by
    change level ≤ Nat.clog base (maximum + 1) at hlevel
    omega
  have hp := Nat.pow_lt_of_lt_clog hlt
  omega

/-- Sampled positive levels begin before the upper bound. -/
theorem lower_eq_pow (maximum base level : ℕ) (hl : 0 < level)
    (hlevel : level ≤ lastLevel maximum base) :
    lower maximum base level = base ^ (level - 1) :=
  Nat.min_eq_right (lower_pow_le maximum base level hl hlevel)

end SampLib.LogUniform
