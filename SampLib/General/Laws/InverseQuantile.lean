import SampLib.Combinatorial.Laws.Choice

/-! # Quantiles on a uniform interior grid -/

open scoped ENNReal

namespace SampLib.InverseQuantile

noncomputable section

open MeasureTheory

variable {α : Type _} [MeasurableSpace α]

/-- Push the uniform interior-grid positions through the supplied quantile. -/
def law (n : ℕ) [NeZero n] (quantile : Fin n → α) : Measure α :=
  (Choice.law n).map quantile

instance (n : ℕ) [NeZero n] (quantile : Fin n → α) :
    IsProbabilityMeasure (law n quantile) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- The quantile expectation is the average over the interior ranks. -/
theorem expectation (n : ℕ) [NeZero n] (quantile : Fin n → α)
    (F : α → ℝ≥0∞) (hF : Measurable F) :
    (∑ k ∈ Finset.range n, F (quantile (Choice.position n k))) / n =
      ∫⁻ x, F x ∂law n quantile := by
  rw [law, lintegral_map hF (measurable_of_countable _), Choice.lintegral_law]

end

end SampLib.InverseQuantile
