import SampLib.Uniform.Laws.RealCoin

/-! # Laws of the complement coin

Negating the result swaps the two Bernoulli masses, so the output bias is `1-p`.
-/

open scoped ENNReal

namespace SampLib.Complement

noncomputable section

abbrev law (p : unitInterval) := RealCoin.law (unitInterval.symm p)

/-- Negating the result swaps the two Bernoulli masses. -/
theorem expectation_preservation (p : unitInterval) (F : Bool → ℝ≥0∞) :
    ∫⁻ b, F (!b) ∂RealCoin.law p = ∫⁻ b, F b ∂law p := by
  simp [law, RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf,
    unitInterval.coe_symm_eq, add_comm]

end

end SampLib.Complement
