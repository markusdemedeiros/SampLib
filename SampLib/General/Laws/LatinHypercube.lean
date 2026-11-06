import SampLib.General.Laws.LatinHypercube1D
import SampLib.General.Laws.RepeatedSupport

/-! # Latin hypercube law

Independent shuffled columns, transposed into point order.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.LatinHypercube

noncomputable section

/-- Read a row, with a total default outside the fixed-length column support. -/
def row (columns : List (List ℤ)) (i : ℕ) : List ℤ :=
  columns.map (fun xs => xs[i]?.getD 0)

/-- Consecutive rows of the sampled columns. -/
def rowsFrom (columns : List (List ℤ)) (i : ℕ) : ℕ → List (List ℤ)
  | 0 => []
  | n + 1 => row columns i :: rowsFrom columns (i + 1) n

/-- Independent shuffled columns, transposed into point order. -/
def law (scale count : ℕ) (hc : 0 < count) (h : count ≤ scale) (dimension : ℕ) :
    Measure (List (List ℤ)) :=
  (SampleWithReplacement.law (LatinHypercube1D.law scale count hc h) dimension).map
    (fun columns => rowsFrom (List.ofFn columns) 0 count)

instance (scale count : ℕ) (hc : 0 < count) (h : count ≤ scale) (dimension : ℕ) :
    IsProbabilityMeasure (law scale count hc h dimension) := by unfold law; infer_instance

/-- The transpose is a deterministic pushforward of the independent column law. -/
theorem expectation (scale count : ℕ) (hc : 0 < count) (h : count ≤ scale)
    (dimension : ℕ) (F : List (List ℤ) → ℝ≥0∞) :
    ∫⁻ columns, F (rowsFrom (List.ofFn columns) 0 count)
        ∂SampleWithReplacement.law (LatinHypercube1D.law scale count hc h) dimension =
      ∫⁻ ys, F ys ∂law scale count hc h dimension := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

/-- Every sampled column has one entry for each stratum. -/
theorem columns_valid (scale count : ℕ) (hc : 0 < count) (h : count ≤ scale)
    (dimension : ℕ) :
    ∀ᵐ columns ∂SampleWithReplacement.law (LatinHypercube1D.law scale count hc h) dimension,
      ∀ i, (columns i).length = count :=
  SampleWithReplacement.all_ae _ _ (LatinHypercube1D.length_ae scale count hc h) dimension

end

end SampLib.LatinHypercube
