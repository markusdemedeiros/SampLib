import SampLib.Bernoulli.Laws.EvenParity
import SampLib.Bernoulli.Laws.VonNeumann

/-! # Laws of the reciprocal Bernoulli factory

A fair flip either returns `true`, or tests the input coin and retries on failure. This
module proves that one round preserves the reciprocal bias `1/(1+p)` and spends at most the
retry credit.
-/

open ENNReal (ofReal ofReal_add ofReal_mul)
open scoped ENNReal NNReal

namespace SampLib.OneDivOnePlus

open RealCoin (pmf lintegral_law)

noncomputable section

/-- The reciprocal bias `1/(1+p)`, shared with the even-parity factory. -/
abbrev bias := EvenParity.bias
abbrev law (p : unitInterval) := RealCoin.law (bias p)
abbrev credit (p : unitInterval) := RealCoin.credit (bias p)

private def retryProbability (p : unitInterval) : ℝ := (1 - (p : ℝ)) / 2

/-- Credit assigned to the input coin after a failed fair flip. -/
def coinCredit (p : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F false else credit p F + 2 * ε

/-- Credit assigned to the fair flip. -/
def fairCredit (p : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F true else ∫⁻ a, coinCredit p F ε a ∂RealCoin.law p

/-- The fair/input mixture preserves the reciprocal bias and spends at most `ε` on retrying. -/
theorem expectation (p : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ b, fairCredit p F ε b ∂RealCoin.law VonNeumann.fairBias ≤ credit p F + ε := by
  have hp0 := p.2.1
  have hp1 := sub_nonneg.mpr p.2.2
  have hq : 0 ≤ retryProbability p := div_nonneg hp1 (by norm_num)
  have ht : 0 ≤ 1 / (1 + (p : ℝ)) := (bias p).2.1
  have hf : 0 ≤ 1 - 1 / (1 + (p : ℝ)) := sub_nonneg.mpr (bias p).2.2
  have hsplit : ofReal (retryProbability p) =
      ofReal (1 / 2 : ℝ) * pmf p false := by
    rw [show retryProbability p = (1 / 2 : ℝ) * (1 - (p : ℝ)) by
      dsimp [retryProbability]; ring, ofReal_mul (by norm_num)]
    simp [pmf]
  have htrue : ofReal (retryProbability p) * pmf (bias p) true + ofReal (1 / 2 : ℝ) =
      pmf (bias p) true := by
    change ofReal (retryProbability p) * ofReal (1 / (1 + (p : ℝ))) +
      ofReal (1 / 2 : ℝ) = ofReal (1 / (1 + (p : ℝ)))
    rw [← ofReal_mul hq,
      ← ofReal_add (mul_nonneg hq ht) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    dsimp [retryProbability, bias, EvenParity.bias]
    field_simp
    ring
  have hfalse : ofReal (retryProbability p) * pmf (bias p) false +
      ofReal (1 / 2 : ℝ) * pmf p true = pmf (bias p) false := by
    change ofReal (retryProbability p) * ofReal (1 - 1 / (1 + (p : ℝ))) +
      ofReal (1 / 2 : ℝ) * ofReal (p : ℝ) = ofReal (1 - 1 / (1 + (p : ℝ)))
    rw [← ofReal_mul hq, ← ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ofReal_add (mul_nonneg hq hf) (mul_nonneg (by norm_num) hp0)]
    congr 1
    dsimp [retryProbability, bias, EvenParity.bias]
    field_simp
    ring
  have hterm : ofReal (retryProbability p) * 2 ≤ 1 := by
    calc
      _ = ofReal (retryProbability p * 2) := by rw [ofReal_mul hq]; norm_num
      _ ≤ _ := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        dsimp [retryProbability]
        nlinarith
  calc
    _ = (ofReal (retryProbability p) * pmf (bias p) true + ofReal (1 / 2 : ℝ)) * F true +
        (ofReal (retryProbability p) * pmf (bias p) false +
          ofReal (1 / 2 : ℝ) * pmf p true) * F false +
        (ofReal (retryProbability p) * 2) * ε := by
      rw [hsplit]
      norm_num [fairCredit, coinCredit, lintegral_law, RealCoin.credit, pmf, VonNeumann.fairBias]
      ring
    _ ≤ _ := by
      rw [htrue, hfalse]
      exact add_le_add le_rfl (mul_le_of_le_one_left' hterm)

end

end SampLib.OneDivOnePlus
