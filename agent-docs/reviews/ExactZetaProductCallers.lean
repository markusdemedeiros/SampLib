import SampLib.Constants.Laws.ZetaProductIntegralLaw

open MeasureTheory
open scoped ENNReal

namespace SampLib.ExactZetaProductCallers

noncomputable section

example : (∫ u, (ZetaProductIntegral.product u) ^ 1 ∂ZetaProductIntegral.law 2) = 1 / 4 := by
  rw [ZetaProductIntegral.moment]
  norm_num

example : (∫ u, (ZetaProductIntegral.product u) ^ 2 ∂ZetaProductIntegral.law 3) = 1 / 27 := by
  rw [ZetaProductIntegral.moment]
  norm_num

example : (ZetaRelated.marginalBias 2 : ℝ) = (riemannZeta 2).re / 2 := by
  have h := ZetaRelated.marginalBias_coe (n := 2) (by omega)
  rw [← ZetaProductIntegral.eta_factor] at h
  norm_num at h
  linear_combination h

example : (ZetaRelated.marginalBias 3 : ℝ) = 3 / 4 * (riemannZeta 3).re := by
  have h := ZetaRelated.marginalBias_coe (n := 3) (by omega)
  rw [← ZetaProductIntegral.eta_factor] at h
  norm_num at h
  exact h

theorem arbitrary_credit (n : ℕ) (F : Bool → ℝ≥0∞) :
    LatentReal.LatentCoin.credit (UniformVector.world n) (UniformVector.initial n)
      (ZetaRelated.conditionalBias n) (fun b _ => F b) =
        ∫⁻ b, F b ∂RealCoin.law (ZetaRelated.marginalBias n) := by
  rw [ZetaRelated.expectation_eta, RealCoin.lintegral_law]

theorem infinite_success (n : ℕ) :
    LatentReal.LatentCoin.credit (UniformVector.world n) (UniformVector.initial n)
      (ZetaRelated.conditionalBias n) (fun b _ => if b then ∞ else 0) =
        ENNReal.ofReal (ZetaRelated.marginalBias n : ℝ) * ∞ := by
  rw [ZetaRelated.expectation_eta]
  simp [RealCoin.credit, RealCoin.pmf]

theorem infinite_failure (n : ℕ) :
    LatentReal.LatentCoin.credit (UniformVector.world n) (UniformVector.initial n)
      (ZetaRelated.conditionalBias n) (fun b _ => if b then 0 else ∞) =
        ENNReal.ofReal (1 - (ZetaRelated.marginalBias n : ℝ)) * ∞ := by
  rw [ZetaRelated.expectation_eta]
  simp [RealCoin.credit, RealCoin.pmf]

#print axioms ZetaProductIntegral.moment
#print axioms ZetaProductIntegral.integral_eq_zeta
#print axioms ZetaRelated.conditionalBias_ae
#print axioms ZetaRelated.marginalBias_coe
#print axioms ZetaRelated.law_eq_coin
#print axioms ZetaRelated.expectation_eta
#print axioms arbitrary_credit
#print axioms infinite_success
#print axioms infinite_failure

end

end SampLib.ExactZetaProductCallers
