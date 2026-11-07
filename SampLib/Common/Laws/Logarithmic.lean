module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-! # The reciprocal-weighted geometric series -/

namespace ProbabilityTheory

/-- Weighting positive geometric counts by their reciprocals gives `p log(1/p)`. -/
theorem hasSum_geometric_reciprocal_succ {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    HasSum (fun n : ℕ => p * ((1 - p) ^ (n + 1) / (n + 1))) (p * Real.log (1 / p)) := by
  have hq : |1 - p| < 1 := by rw [abs_of_nonneg (sub_nonneg.mpr hp1)]; linarith
  simpa using (Real.hasSum_pow_div_log_of_abs_lt_one hq).mul_left p

end ProbabilityTheory
