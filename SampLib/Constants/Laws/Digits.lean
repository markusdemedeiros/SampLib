module

public import Mathlib.Analysis.Real.OfDigits

@[expose] public section

/-! # Leading digits of a base-`b` expansion -/

namespace Real

/-- Removing the first digit leaves the fractional tail, scaled by the base. -/
theorem ofDigits_cons {b : ℕ} (d : ℕ → Fin b) :
    ofDigits d = ((d 0 : ℝ) + ofDigits (fun n => d (n + 1))) / b := by
  have h := ofDigits_eq_sum_add_ofDigits d 1
  simpa [ofDigitsTerm, div_eq_mul_inv, add_mul, mul_add, mul_comm] using h

end Real
