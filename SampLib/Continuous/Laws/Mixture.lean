module

public import SampLib.Uniform.Laws.RealCoin

@[expose] public section

/-! # Mixture of two laws selected by a Bernoulli coin -/

open scoped ENNReal

namespace SampLib.Mixture

noncomputable section

section mathematics

open MeasureTheory Measure

variable {α : Type _} [MeasurableSpace α]

/-- Select `μ` with probability `p` and `ν` otherwise. -/
def law (p : unitInterval) (μ ν : Measure α) : Measure α :=
  (RealCoin.pmf p true • μ) + (RealCoin.pmf p false • ν)

instance (p : unitInterval) (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (law p μ ν) where
  measure_univ := by simpa [law] using RealCoin.pmf_sum p

/-- Mixture expectation is the coin expectation of component expectations. -/
theorem expectation_preservation (p : unitInterval) (μ ν : Measure α)
    (F : α → ℝ≥0∞) :
    ∫⁻ x, F x ∂law p μ ν =
      RealCoin.credit p (fun b => if b then ∫⁻ x, F x ∂μ else ∫⁻ x, F x ∂ν) := by
  simp [law, RealCoin.credit, smul_eq_mul]

end mathematics

end

end SampLib.Mixture
