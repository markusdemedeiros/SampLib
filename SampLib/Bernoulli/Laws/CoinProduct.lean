import SampLib.Uniform.Laws.RealCoin

/-! # Laws of the coin product

The second coin runs only after the first succeeds, so the output bias is `pq`.
-/

open ENNReal (ofReal_add ofReal_mul)
open scoped ENNReal

namespace SampLib.CoinProduct

noncomputable section

abbrev law (p q : unitInterval) := RealCoin.law (p * q)

/-- Credit for the second draw is needed only after a successful first draw. -/
def firstCredit (q : unitInterval) (F : Bool → ℝ≥0∞) (a : Bool) : ℝ≥0∞ :=
  if a then ∫⁻ b, F b ∂RealCoin.law q else F false

/-- The failure mass is `p(1-q) + (1-p) = 1-pq`. -/
theorem expectation_preservation (p q : unitInterval) (F : Bool → ℝ≥0∞) :
    ∫⁻ a, firstCredit q F a ∂RealCoin.law p = ∫⁻ b, F b ∂law p q := by
  have hfalse : 1 - (p : ℝ) * q = (p : ℝ) * (1 - q) + (1 - p) := by ring
  simp [law, firstCredit, RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]
  rw [hfalse, ofReal_add (mul_nonneg p.2.1 (sub_nonneg.mpr q.2.2))
    (sub_nonneg.mpr p.2.2)]
  simp only [ofReal_mul p.2.1]
  ring

end

end SampLib.CoinProduct
