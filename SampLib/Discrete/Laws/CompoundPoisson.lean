import SampLib.Common.Laws.PoissonThinning

/-! # Compound Poisson law

A Poisson number of independent signed integer jumps defines the law.
Conditioning on the number of jumps preserves every continuation credit.
-/

open scoped ENNReal NNReal

namespace SampLib.CompoundPoisson

noncomputable section

open MeasureTheory Measure

variable {α : Type _} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

/-- Sum of independent integer-valued jumps. -/
def sumLaw (μ : Measure α) (jump : α → ℤ) : ℕ → Measure ℤ
  | 0 => dirac 0
  | n + 1 => (μ.prod (sumLaw μ jump n)).map (fun z => jump z.1 + z.2)

instance (μ : Measure α) [IsProbabilityMeasure μ] (jump : α → ℤ) (n : ℕ) :
    IsProbabilityMeasure (sumLaw μ jump n) := by
  induction n with
  | zero => dsimp [sumLaw]; infer_instance
  | succ n IH =>
    let := IH
    constructor
    rw [sumLaw, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

def sumCredit (μ : Measure α) (jump : α → ℤ) (n : ℕ) (total : ℤ)
    (F : ℤ → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ z, F (total + z) ∂sumLaw μ jump n

omit [Countable α] [MeasurableSingletonClass α] in
@[simp] theorem sumCredit_zero (μ : Measure α) (jump : α → ℤ) (total : ℤ)
    (F : ℤ → ℝ≥0∞) : sumCredit μ jump 0 total F = F total := by
  simp [sumCredit, sumLaw]

/-- The first independent jump advances the accumulator and leaves the tail sum. -/
theorem sum_expectation (μ : Measure α) [IsProbabilityMeasure μ] (jump : α → ℤ)
    (n : ℕ) (total : ℤ) (F : ℤ → ℝ≥0∞) :
    sumCredit μ jump (n + 1) total F =
      ∫⁻ x, sumCredit μ jump n (total + jump x) F ∂μ := by
  rw [sumCredit, sumLaw,
    lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]
  simp only [sumCredit, add_assoc]

/-- A Poisson number of independent jumps defines the compound Poisson law. -/
def law (rate : ℝ≥0) (μ : Measure α) (jump : α → ℤ) : Measure ℤ :=
  (ProbabilityTheory.poissonMeasure rate).bind (sumLaw μ jump)

instance (rate : ℝ≥0) (μ : Measure α) [IsProbabilityMeasure μ] (jump : α → ℤ) :
    IsProbabilityMeasure (law rate μ jump) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ
      (measurable_of_countable _).aemeasurable]
    simp

omit [Countable α] [MeasurableSingletonClass α] in
/-- Conditioning on the number of jumps preserves arbitrary continuation credits. -/
theorem expectation (rate : ℝ≥0) (μ : Measure α) [IsProbabilityMeasure μ]
    (jump : α → ℤ) (F : ℤ → ℝ≥0∞) :
    (∫⁻ n, sumCredit μ jump n 0 F ∂ProbabilityTheory.poissonMeasure rate) =
      ∫⁻ z, F z ∂law rate μ jump := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]
  simp only [sumCredit, zero_add]

end

end SampLib.CompoundPoisson
