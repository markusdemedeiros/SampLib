import Metrology.ProbLang.Discrete
import Mathlib.MeasureTheory.Measure.Prod

/-! # Independent list map law -/

open MeasureTheory Measure
open scoped ENNReal

namespace SampLib.ListMapSampling

noncomputable section

variable {α β : Type _} [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]

/-- Draw one independent result from the kernel at each list entry. -/
def law (μ : α → Measure β) : List α → Measure (List β)
  | [] => dirac []
  | x :: xs => ((law μ xs).prod (μ x)).map (fun p => p.2 :: p.1)

instance (μ : α → Measure β) [∀ x, IsProbabilityMeasure (μ x)] (xs : List α) :
    IsProbabilityMeasure (law μ xs) := by
  induction xs with
  | nil => dsimp [law]; infer_instance
  | cons x xs IH =>
    let := IH
    constructor
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

@[simp] theorem law_dirac (f : α → β) (xs : List α) :
    law (fun x => dirac (f x)) xs = dirac (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons x xs IH =>
    simp [law, IH, Measure.dirac_prod_dirac,
      Measure.map_dirac' (measurable_of_countable _)]

/-- The independent list expectation separates its tail and head kernel. -/
theorem expectation (μ : α → Measure β) [∀ x, IsProbabilityMeasure (μ x)]
    (x : α) (xs : List α) (F : List β → ℝ≥0∞) :
    ∫⁻ ys, ∫⁻ y, F (y :: ys) ∂μ x ∂law μ xs = ∫⁻ ys, F ys ∂law μ (x :: xs) := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]

end

end SampLib.ListMapSampling
