import SampLib.Common.Laws.FractionalPowerCore

/-! # Laws of Mendo's fractional-power factory

The factory with rational exponent `a/b` returns `true` with probability `p^(a/b)`.
-/

namespace SampLib.FractionalPower

noncomputable section

/-- The rational exponent accepted by the original factory. -/
def exponent (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) : unitInterval :=
  ⟨(a : ℝ) / b, by positivity,
    (div_le_one (show (0 : ℝ) < b by exact_mod_cast lt_of_lt_of_le ha hab)).mpr
      (by exact_mod_cast hab)⟩

abbrev bias (p : unitInterval) (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) : unitInterval :=
  powerBias p (exponent a b ha hab)

end

end SampLib.FractionalPower
