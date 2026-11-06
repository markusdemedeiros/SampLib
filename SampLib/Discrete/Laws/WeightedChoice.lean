import SampLib.Uniform.Laws.UniformInt

/-! # Cumulative weighted choice law

A uniform rank falls in one block per category, so each category has
probability its weight divided by the total. Zero weights give empty blocks.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace SampLib.WeightedChoice

noncomputable section

/-- The category containing a rank in the concatenation of the weight blocks. -/
def category : List ℕ → ℕ → ℕ
  | [], _ => 0
  | w :: ws, k => if k < w then 0 else category ws (k - w) + 1

/-- Unnormalized categorical expectation, with one summand per list position. -/
def weightedSum : List ℕ → (ℕ → ℝ≥0∞) → ℝ≥0∞
  | [], _ => 0
  | w :: ws, F => w * F 0 + weightedSum ws (fun i => F (i + 1))

/-- Each block contributes its length times the category's continuation credit. -/
theorem rank_partition (ws : List ℕ) (F : ℕ → ℝ≥0∞) :
    ∑ k ∈ range ws.sum, F (category ws k) = weightedSum ws F := by
  induction ws generalizing F with
  | nil => simp [weightedSum]
  | cons w ws IH =>
    rw [List.sum_cons, sum_range_add]
    have first : (∑ k ∈ range w, F (category (w :: ws) k)) = w * F 0 := by
      simp only [category]
      calc
        _ = ∑ k ∈ range w, F 0 :=
          sum_congr rfl fun k hk => by rw [ite_eq_left (mem_range.mp hk)]
        _ = _ := by simp [nsmul_eq_mul]
    rw [first]
    simp only [category, Nat.not_lt.mpr (Nat.le_add_right w _), ↓reduceIte,
      Nat.add_sub_cancel_left]
    rw [IH (fun i => F (i + 1))]
    rfl

/-- The categorical law: a category has probability its weight divided by the total. -/
def law (ws : List ℕ) : Measure ℕ :=
  (UniformInt.law ws.sum).map (category ws)

instance (ws : List ℕ) [NeZero ws.sum] : IsProbabilityMeasure (law ws) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Normalized categorical expectation; credits may be infinite. -/
theorem lintegral_law (ws : List ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ i, F i ∂law ws = weightedSum ws F / ws.sum := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    UniformInt.lintegral_law, rank_partition]

@[simp] theorem weightedSum_zero (ws : List ℕ) : weightedSum ws (fun _ => 0) = 0 := by
  induction ws with
  | nil => rfl
  | cons w ws IH => simp [weightedSum, IH]

private theorem weightedSum_singleton (ws : List ℕ) (i : ℕ) :
    weightedSum ws (fun j => if j = i then 1 else 0) = (ws[i]?.getD 0 : ℝ≥0∞) := by
  induction ws generalizing i with
  | nil => simp [weightedSum]
  | cons w ws IH =>
    cases i with
    | zero => simp [weightedSum]
    | succ i => simpa [weightedSum] using IH i

/-- Zero and out-of-range weights have zero probability. -/
theorem law_singleton (ws : List ℕ) (i : ℕ) :
    law ws {i} = (ws[i]?.getD 0 : ℝ≥0∞) / ws.sum := by
  rw [← lintegral_indicator_one (measurableSet_singleton i)]
  simpa [Set.indicator, weightedSum_singleton] using
    lintegral_law ws (fun j => if j = i then 1 else 0)

end

end SampLib.WeightedChoice
