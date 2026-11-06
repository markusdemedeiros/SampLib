import SampLib.Distributions.ConditionalCoin
import SampLib.Distributions.LatentReal.UniformVectorCoin
import SampLib.LatentCoinReciprocal

/-! # The zeta coin's conditional and marginal laws -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.ZetaRelated

noncomputable section

/-- Conditional on the cached uniforms, the reciprocal factory has this exact bias. -/
def conditionalBias (n : ℕ) : (Fin n → ℝ) → unitInterval :=
  LatentReal.CoinReciprocal.bias (UniformVector.productBias (List.ofFn id))

theorem measurable_conditionalBias (n : ℕ) : Measurable (conditionalBias n) :=
  LatentReal.CoinReciprocal.measurable_bias (UniformVector.measurable_productBias _)

/-- Average only after all calls on the persistent bag list have finished. -/
def law (n : ℕ) : Measure Bool :=
  ConditionalCoin.law (UniformVector.law (UniformVector.initial n)) (conditionalBias n)

instance (n : ℕ) : IsProbabilityMeasure (law n) := by
  let : Fact (Measurable (conditionalBias n)) := ⟨measurable_conditionalBias n⟩
  unfold law
  infer_instance

/-- Marginalization preserves arbitrary Boolean continuation credit. -/
theorem expectation (n : ℕ) (F : Bool → ℝ≥0∞) :
    (∫⁻ b, F b ∂law n) =
      LatentReal.LatentCoin.credit (UniformVector.world n) (UniformVector.initial n)
        (conditionalBias n) (fun b _ => F b) :=
  ConditionalCoin.lintegral_law _ _ (measurable_conditionalBias n) F

/-- A returned bit carries constant credit under every refined joint posterior. -/
theorem posterior_const (n : ℕ) (p : Fin n → List Bool) (c : ℝ≥0∞) :
    (∫⁻ _ : Fin n → ℝ, c ∂(UniformVector.world n).posterior p) = c := by
  simp [UniformVector.world]

end

end SampLib.ZetaRelated
