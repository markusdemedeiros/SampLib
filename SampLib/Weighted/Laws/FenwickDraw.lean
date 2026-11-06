import SampLib.Discrete.Laws.WeightedChoice

/-! # Expectation for Fenwick-tree categorical draws -/

open scoped ENNReal

namespace SampLib.FenwickDraw

/-- Uniform cumulative rank has the categorical expectation, including infinite credits. -/
theorem expectation {n : ℕ} (w : Fin n → ℕ) (F : ℕ → ℝ≥0∞) :
    (∑ rank ∈ Finset.range (List.ofFn w).sum,
        F (WeightedChoice.category (List.ofFn w) rank)) / (List.ofFn w).sum =
      ∫⁻ i, F i ∂WeightedChoice.law (List.ofFn w) := by
  rw [WeightedChoice.rank_partition, WeightedChoice.lintegral_law]

end SampLib.FenwickDraw
