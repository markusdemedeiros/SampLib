import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Prod

/-! # Stopped sum law -/

open MeasureTheory Measure
open scoped ENNReal

namespace SampLib.StoppedSum

noncomputable section

/-- The finite convolution of the summand law, including the empty sum. -/
def sumLaw (μ : Measure ℤ) : ℕ → Measure ℤ
  | 0 => dirac 0
  | n + 1 => ((sumLaw μ n).prod μ).map (fun z => z.2 + z.1)

instance (μ : Measure ℤ) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (sumLaw μ n) := by
  induction n with
  | zero => dsimp [sumLaw]; infer_instance
  | succ n IH =>
    let := IH
    constructor
    rw [sumLaw, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Mix the finite convolutions against the independent stopping count. -/
def law (ν : Measure ℕ) (μ : Measure ℤ) : Measure ℤ := ν.bind (sumLaw μ)

instance (ν : Measure ℕ) [IsProbabilityMeasure ν] (μ : Measure ℤ)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (law ν μ) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
    simp

/-- The convolution supplies the two successive continuation expectations. -/
theorem sum_expectation (μ : Measure ℤ) [IsProbabilityMeasure μ] (n : ℕ)
    (F : ℤ → ℝ≥0∞) :
    ∫⁻ rest, ∫⁻ x, F (x + rest) ∂μ ∂sumLaw μ n =
      ∫⁻ z, F z ∂sumLaw μ (n + 1) := by
  rw [sumLaw, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]

/-- Conditioning on the stopping count needs no moment or credit bound. -/
theorem expectation (ν : Measure ℕ) [IsProbabilityMeasure ν] (μ : Measure ℤ)
    [IsProbabilityMeasure μ] (F : ℤ → ℝ≥0∞) :
    ∫⁻ n, ∫⁻ z, F z ∂sumLaw μ n ∂ν = ∫⁻ z, F z ∂law ν μ := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]

end

end SampLib.StoppedSum
