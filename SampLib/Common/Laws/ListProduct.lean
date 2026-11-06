import SampLib.Combinatorial.SampleWithReplacement

/-! # Independent lists with coordinate-dependent laws -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.ListProduct

noncomputable section

variable {α : Type _} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The independent coordinate laws, starting at coordinate `i`. -/
def law (μ : ℕ → Measure α) (i : ℕ) : ℕ → Measure (List α)
  | 0 => Measure.dirac []
  | n + 1 => ((law μ (i + 1) n).prod (μ i)).map (fun p => p.2 :: p.1)

omit [Countable α] [MeasurableSingletonClass α] in
@[simp] theorem constant_start (μ : Measure α) (i n : ℕ) :
    law (fun _ => μ) i n = law (fun _ => μ) 0 n := by
  induction n generalizing i with
  | zero => rfl
  | succ n IH => simp only [law, IH]

instance (μ : ℕ → Measure α) [∀ i, IsProbabilityMeasure (μ i)] (i n : ℕ) :
    IsProbabilityMeasure (law μ i n) := by
  induction n generalizing i with
  | zero => dsimp [law]; infer_instance
  | succ n IH =>
    let := IH (i + 1)
    constructor
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Fubini separates the tail draw from the new coordinate. -/
theorem expectation (μ : ℕ → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (i n : ℕ) (F : List α → ℝ≥0∞) :
    ∫⁻ ys, ∫⁻ x, F (x :: ys) ∂μ i ∂law μ (i + 1) n =
      ∫⁻ ys, F ys ∂law μ i (n + 1) := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]

end

end SampLib.ListProduct
