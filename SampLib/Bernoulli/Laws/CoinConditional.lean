import SampLib.Uniform.Laws.RealCoin

/-! # Laws of the conditional coin

The selector picks the left coin with probability `r`, so the output bias is the convex
combination `(1-r)q + rp`.
-/

open ENNReal (ofReal_add ofReal_mul)
open scoped ENNReal

namespace SampLib.CoinConditional

noncomputable section

/-- Bias `(1-r)q + rp`, with `r` the selector's probability. -/
abbrev bias (p q r : unitInterval) := Set.Icc.convexComb q p r

abbrev law (p q r : unitInterval) := RealCoin.law (bias p q r)

def firstCredit (p q : unitInterval) (F : Bool → ℝ≥0∞) (a : Bool) : ℝ≥0∞ :=
  if a then ∫⁻ b, F b ∂RealCoin.law p else ∫⁻ b, F b ∂RealCoin.law q

/-- The selector mixes the two success and failure masses with weights `r` and `1-r`. -/
theorem expectation_preservation (p q r : unitInterval) (F : Bool → ℝ≥0∞) :
    ∫⁻ a, firstCredit p q F a ∂RealCoin.law r = ∫⁻ b, F b ∂law p q r := by
  have hfalse : 1 - ((1 - (r : ℝ)) * q + r * p) =
      (1 - r) * (1 - (q : ℝ)) + r * (1 - (p : ℝ)) := by ring
  simp [law, bias, firstCredit, RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]
  rw [hfalse,
    ofReal_add (mul_nonneg (sub_nonneg.mpr r.2.2) q.2.1) (mul_nonneg r.2.1 p.2.1),
    ofReal_add (mul_nonneg (sub_nonneg.mpr r.2.2) (sub_nonneg.mpr q.2.2))
      (mul_nonneg r.2.1 (sub_nonneg.mpr p.2.2))]
  simp only [ofReal_mul (sub_nonneg.mpr r.2.2), ofReal_mul r.2.1]
  ring


/-- The conditional coin as a credit identity. -/
theorem credit_mixture (p q r : unitInterval) (F : Bool → ℝ≥0∞) :
    RealCoin.credit r (fun b => if b then RealCoin.credit p F else RealCoin.credit q F) =
      RealCoin.credit (bias p q r) F := by
  simpa only [RealCoin.lintegral_law, firstCredit, law] using expectation_preservation p q r F

end

end SampLib.CoinConditional
