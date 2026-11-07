import SampLib.Combinatorial.Laws.SampleWithReplacement
import Metrology.ProbLang.Discrete

/-! # Random walk path law -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.RandomWalkPath

noncomputable section

/-- Scan the independent increment vector, retaining the initial position. -/
def law (μ : Measure ℤ) (initial : ℤ) (steps : ℕ) : Measure (List ℤ) :=
  (SampleWithReplacement.law μ steps).map (fun xs => (List.ofFn xs).scanl (· + ·) initial)

instance (μ : Measure ℤ) [IsProbabilityMeasure μ] (initial : ℤ) (steps : ℕ) :
    IsProbabilityMeasure (law μ initial steps) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- The first increment shifts the remaining path and preserves the starting point. -/
theorem expectation (μ : Measure ℤ) [IsProbabilityMeasure μ] (initial : ℤ)
    (steps : ℕ) (F : List ℤ → ℝ≥0∞) :
    ∫⁻ x, ∫⁻ ys, F (initial :: ys) ∂law μ (initial + x) steps ∂μ =
      ∫⁻ ys, F ys ∂law μ initial (steps + 1) := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    SampleWithReplacement.lintegral_law_succ μ steps _ (measurable_of_countable _)]
  simp only [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    List.ofFn_succ, List.scanl_cons, Fin.cons_zero, Fin.cons_succ]

end

end SampLib.RandomWalkPath
