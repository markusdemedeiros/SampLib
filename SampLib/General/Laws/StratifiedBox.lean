import SampLib.Combinatorial.Laws.SampleWithReplacement
import SampLib.Common.Laws.ListProduct
import SampLib.General.Laws.StratifiedCell

/-! # Stratified box law

Every cell receives the requested number of independent points. The cell laws are
flattened in cell order, as in the implementation.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.StratifiedBox

noncomputable section

/-- The independent points belonging to one cell. -/
def chunkLaw (scale bins : ℕ) (hb : 0 < bins) (h : bins ≤ scale)
    (dimension perCell cell : ℕ) : Measure (List (List ℤ)) :=
  (SampleWithReplacement.law (StratifiedCell.law scale bins hb h dimension cell) perCell).map
    (fun ys => List.ofFn ys)

instance (scale bins : ℕ) (hb : 0 < bins) (h : bins ≤ scale)
    (dimension perCell cell : ℕ) :
    IsProbabilityMeasure (chunkLaw scale bins hb h dimension perCell cell) := by
  unfold chunkLaw
  infer_instance

/-- Consecutive independent cell chunks, concatenated in increasing cell order. -/
def lawFrom (scale bins : ℕ) (hb : 0 < bins) (h : bins ≤ scale)
    (dimension perCell cell remaining : ℕ) : Measure (List (List ℤ)) :=
  (ListProduct.law (chunkLaw scale bins hb h dimension perCell) cell remaining).map List.flatten

instance (scale bins : ℕ) (hb : 0 < bins) (h : bins ≤ scale)
    (dimension perCell cell remaining : ℕ) :
    IsProbabilityMeasure (lawFrom scale bins hb h dimension perCell cell remaining) := by
  unfold lawFrom
  infer_instance

/-- The joint law of the entire jittered grid. -/
def law (scale bins : ℕ) (hb : 0 < bins) (h : bins ≤ scale) (dimension perCell : ℕ) :
    Measure (List (List ℤ)) :=
  lawFrom scale bins hb h dimension perCell 0 (bins ^ dimension)

instance (scale bins : ℕ) (hb : 0 < bins) (h : bins ≤ scale) (dimension perCell : ℕ) :
    IsProbabilityMeasure (law scale bins hb h dimension perCell) := by
  unfold law
  infer_instance

/-- Concatenation transports the two independent continuation expectations. -/
theorem expectation (scale bins : ℕ) (hb : 0 < bins) (h : bins ≤ scale)
    (dimension perCell cell n : ℕ) (F : List (List ℤ) → ℝ≥0∞) :
    ∫⁻ ys, ∫⁻ chunk, F (chunk ++ ys) ∂chunkLaw scale bins hb h dimension perCell cell
        ∂lawFrom scale bins hb h dimension perCell (cell + 1) n =
      ∫⁻ ys, F ys ∂lawFrom scale bins hb h dimension perCell cell (n + 1) := by
  simp only [lawFrom]
  rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  simpa only [List.flatten_cons] using
    ListProduct.expectation (chunkLaw scale bins hb h dimension perCell) cell n
      (fun chunks => F chunks.flatten)

@[simp] theorem expectation_zero (scale bins : ℕ) (hb : 0 < bins) (h : bins ≤ scale)
    (dimension perCell cell : ℕ) (F : List (List ℤ) → ℝ≥0∞) :
    ∫⁻ ys, F ys ∂lawFrom scale bins hb h dimension perCell cell 0 = F [] := by
  rw [lawFrom, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  simp [ListProduct.law]

end

end SampLib.StratifiedBox
