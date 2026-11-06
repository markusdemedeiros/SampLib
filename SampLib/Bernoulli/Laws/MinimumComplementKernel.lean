import SampLib.Bernoulli.Laws.MinimumComplementCoefficients
import SampLib.Bernoulli.Laws.MinimumComplementWalk
import SampLib.Common.Laws.BernoulliMixture
import SampLib.Common.Laws.Binomial
import SampLib.Bernoulli.Laws.CoinMean

/-! # Expectation kernels for the minimum-complement factory

The finite binomial cancellation and the fair-walk harmonic identity lift to
arbitrary nonnegative continuation credits, including infinite credits.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.MinimumComplement

noncomputable section

/-- Success probability after the first-passage walk has selected its index. -/
def conditionalBias (p : unitInterval) (m : ℕ) : unitInterval :=
  ⟨(4 * (p : ℝ) * (1 - p)) ^ m / 2, by
    rw [← Walk.parameter_square]
    constructor
    · positivity
    · have h := pow_le_one₀ (sq_nonneg (Walk.parameter p : ℝ))
        (pow_le_one₀ (Walk.parameter p).2.1 (Walk.parameter p).2.2 (n := 2)) (n := m)
      linarith⟩

private theorem binomial_success (p : unitInterval) (m : ℕ) :
    (∫⁻ j, ENNReal.ofReal (acceptanceBias m j : ℝ)
      ∂Binomial.law p (2 * m + padding m)) = ENNReal.ofReal (conditionalBias p m : ℝ) := by
  rw [Binomial.lintegral_eq_sum]
  calc
    _ = ENNReal.ofReal (∑ j ∈ Finset.range (2 * m + padding m + 1),
        ((2 * m + padding m).choose j : ℝ) * (p : ℝ) ^ j *
          (1 - (p : ℝ)) ^ (2 * m + padding m - j) * acceptance m (padding m) j) := by
      simp only [acceptanceBias]
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ =>
        mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg p.2.1 _))
          (pow_nonneg (sub_nonneg.mpr p.2.2) _))
          (acceptance_mem m (padding m) j (padding_pos m) (padding_large m)).1)]
      apply Finset.sum_congr rfl
      intro j _
      exact (ENNReal.ofReal_mul
        (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg p.2.1 _))
          (pow_nonneg (sub_nonneg.mpr p.2.2) _))).symm
    _ = _ := by rw [binomial_mean]; rfl

/-- The padded binomial stage preserves every continuation expectation. -/
theorem binomial_expectation (p : unitInterval) (m : ℕ) (F : Bool → ℝ≥0∞) :
    (∫⁻ j, RealCoin.credit (acceptanceBias m j) F
      ∂Binomial.law p (2 * m + padding m)) = RealCoin.credit (conditionalBias p m) F :=
  BernoulliMixture.expectation _ _ (measurable_of_countable _) _ (binomial_success p m) F

namespace Walk

/-- The scalar harmonic identity identifies the whole Boolean continuation law. -/
theorem mean_bias (t : unitInterval) (k s : ℕ) :
    CoinMean.bias (bias t k (s + 1)) (bias t (k + 2) (s + 1)) = bias t (k + 1) s := by
  apply Subtype.ext
  change (1 - (1 / 2 : ℝ)) * coefficient t (k + 2) (s + 1) +
    (1 / 2 : ℝ) * coefficient t k (s + 1) = coefficient t (k + 1) s
  linarith [harmonic t k s]

/-- A fair recursive step preserves arbitrary ENNReal continuation credits. -/
theorem expectation (t : unitInterval) (k s : ℕ) (F : Bool → ℝ≥0∞) :
    (∫⁻ a, CoinConditional.firstCredit (bias t k (s + 1)) (bias t (k + 2) (s + 1)) F a
      ∂RealCoin.law VonNeumann.fairBias) = RealCoin.credit (bias t (k + 1) s) F := by
  rw [CoinMean.expectation_preservation, CoinMean.law, mean_bias, RealCoin.lintegral_law]

end Walk

end

end SampLib.MinimumComplement
