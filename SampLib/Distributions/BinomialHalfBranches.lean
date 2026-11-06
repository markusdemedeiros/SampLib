import SampLib.Distributions.Binomial
import SampLib.Samplers.UniformInt
import SampLib.Samplers.VonNeumann

/-! # Adding the last fair bit in an odd half-binomial sample -/

open MeasureTheory Finset
open scoped ENNReal

namespace SampLib.BinomialHalfBranches

noncomputable section

/-- The source samples its right-hand uniform bit before the recursive count. -/
theorem odd_expectation (n : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ bit, ∫⁻ k, F (k + bit) ∂Binomial.law VonNeumann.fairBias n ∂UniformInt.law 2 =
      ∫⁻ k, F k ∂Binomial.law VonNeumann.fairBias (n + 1) := by
  rw [← Binomial.expectation, UniformInt.lintegral_law, RealCoin.lintegral_law]
  simp only [sum_range_succ, range_zero, sum_empty, zero_add, Nat.add_zero,
    RealCoin.credit, Binomial.continuation, Bool.false_eq_true, ↓reduceIte,
    RealCoin.pmf, VonNeumann.fairBias, sub_half]
  norm_num only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  simp only [ENNReal.div_eq_inv_mul]
  ring

/-- The same moment identity at the source's predecessor index. -/
theorem odd_expectation_pred (n : ℕ) (hn : 1 ≤ n) (F : ℕ → ℝ≥0∞) :
    ∫⁻ bit, ∫⁻ k, F (k + bit) ∂Binomial.law VonNeumann.fairBias (n - 1)
      ∂UniformInt.law 2 = ∫⁻ k, F k ∂Binomial.law VonNeumann.fairBias n := by
  simpa only [Nat.sub_add_cancel hn] using odd_expectation (n - 1) F

end

end SampLib.BinomialHalfBranches
