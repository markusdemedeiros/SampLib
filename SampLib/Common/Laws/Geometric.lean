module

public import Mathlib.Probability.Distributions.Geometric

@[expose] public section

/-! # One-step expansion of the geometric expectation -/

open MeasureTheory
open ENNReal (ofReal ofReal_mul ofReal_pow)
open scoped ENNReal

namespace ProbabilityTheory

/-- A geometric expectation separates immediate success from one further failure. -/
theorem lintegral_geometricMeasure_succ (p : unitInterval) (hp : p ≠ 0)
    (F : ℕ → ℝ≥0∞) :
    ∫⁻ n, F n ∂geometricMeasure p = ofReal p * F 0 +
      ofReal (1 - (p : ℝ)) * ∫⁻ n, F (n + 1) ∂geometricMeasure p := by
  have hs (G : ℕ → ℝ≥0∞) :
      ∫⁻ n, G n ∂geometricMeasure p =
        ∑' n, ofReal (1 - (p : ℝ)) ^ n * ofReal p * G n := by
    simp [geometricMeasure_eq hp, lintegral_sum_measure, smul_eq_mul,
      ofReal_mul (pow_nonneg (sub_nonneg.mpr p.2.2) _),
      ofReal_pow (sub_nonneg.mpr p.2.2)]
  rw [hs, hs, tsum_eq_zero_add' ENNReal.summable, ← ENNReal.tsum_mul_left]
  simp only [pow_zero, one_mul]
  congr 1
  apply tsum_congr
  intro n
  rw [pow_succ]
  ring

end ProbabilityTheory
