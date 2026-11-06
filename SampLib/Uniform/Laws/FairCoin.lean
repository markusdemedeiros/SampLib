import SampLib.Bernoulli.Laws.VonNeumann

/-! # The fair coin as the mean of a uniform bit -/

open Finset
open scoped ENNReal

namespace SampLib.FairCoin

noncomputable section

open MeasureTheory

/-- The primitive bit's arithmetic mean equals the fair Bernoulli expectation. -/
theorem expectation (F : Bool → ℝ≥0∞) :
    (∑ n ∈ range 2, F (decide (n = 1))) / 2 =
      ∫⁻ b, F b ∂RealCoin.law VonNeumann.fairBias := by
  rw [RealCoin.lintegral_law]
  norm_num [RealCoin.credit, RealCoin.pmf, VonNeumann.fairBias, sum_range_succ,
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.div_eq_inv_mul,
    mul_add, add_comm]

end

end SampLib.FairCoin
