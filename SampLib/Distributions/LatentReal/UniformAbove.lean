import SampLib.Distributions.LatentReal.UniformThreshold
import SampLib.Distributions.LatentReal.LessKernel
import SampLib.Samplers.Complement

/-! # A fresh uniform above the same owned latent real -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.LatentReal.UniformAbove

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω]

def bias (D : Model Ω S) (ω : Ω) : unitInterval :=
  unitInterval.symm (LatentBernoulli.bias (D.value ω))

theorem measurable_bias (D : Model Ω S) : Measurable (bias D) := by
  exact unitInterval.continuous_symm.measurable.comp
    (LatentBernoulli.measurable_bias.comp D.measurable_value)

def kernel (D : Model Ω S) (G : Bool → Ω → ℝ≥0∞) (z : ℝ × Ω) : ℝ≥0∞ :=
  G (decide (D.value z.2 < z.1)) z.2

theorem measurable_kernel (D : Model Ω S) (G : Bool → Ω → ℝ≥0∞)
    (hG : ∀ b, Measurable (G b)) : Measurable (kernel D G) := by
  change Measurable (Less.outputCredit (ProductModel.right LatentUniform.model D)
    (ProductModel.left LatentUniform.model D) (fun b z => G b z.2))
  exact Less.measurable_outputCredit _ _ _ (fun b => (hG b).comp measurable_snd)

/-- Equality with the fresh nonatomic uniform is null, so reversing the comparison complements it. -/
theorem expectation (D : Model Ω S) (s : S) (G : Bool → Ω → ℝ≥0∞)
    (hG : ∀ b, Measurable (G b)) :
    (∫⁻ z, kernel D G z ∂ProductModel.posterior LatentUniform.model D ([], s)) =
      LatentCoin.credit D s (bias D) G := by
  calc
    _ = ∫⁻ z, UniformThreshold.kernel D (fun b ω => G (!b) ω) z
        ∂ProductModel.posterior LatentUniform.model D ([], s) := by
      apply lintegral_congr_ae
      filter_upwards [UniformThreshold.ae_distinct D s] with z hz
      change z.1 ≠ D.value z.2 at hz
      rcases lt_or_gt_of_ne hz with h | h <;>
        simp [kernel, UniformThreshold.kernel, h, not_lt_of_ge h.le]
    _ = LatentCoin.credit D s (fun ω => LatentBernoulli.bias (D.value ω))
        (fun b ω => G (!b) ω) :=
      UniformThreshold.expectation D s _ (fun b => hG (!b))
    _ = _ := by
      change (∫⁻ ω, RealCoin.credit (LatentBernoulli.bias (D.value ω))
        (fun b => G (!b) ω) ∂D.posterior s) =
        ∫⁻ ω, RealCoin.credit (bias D ω) (fun b => G b ω) ∂D.posterior s
      apply lintegral_congr
      intro ω
      simpa only [Complement.law, RealCoin.lintegral_law, bias] using
        Complement.expectation_preservation (LatentBernoulli.bias (D.value ω)) (fun b => G b ω)

end

end SampLib.LatentReal.UniformAbove
