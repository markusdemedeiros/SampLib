import SampLib.Distributions.WeightedSums
import SampLib.Distributions.WeightedPositiveSupport

/-! # Conditional categorical sampling in consecutive blocks

Choosing a block by its total, then a label by its conditional weight, cancels
the block total. Empty-mass blocks contribute zero, including infinite credits.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.WeightedBlocks

noncomputable section

def chunks (size : ℕ) [NeZero size] : List ℕ → List (List ℕ)
  | [] => []
  | w :: ws => (w :: ws).take size :: chunks size ((w :: ws).drop size)
termination_by ws => ws.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  have := NeZero.pos size
  omega

@[simp] theorem chunks_nil (size : ℕ) [NeZero size] : chunks size [] = [] := by rw [chunks]

theorem chunks_cons (size w : ℕ) [NeZero size] (ws : List ℕ) :
    chunks size (w :: ws) = (w :: ws).take size :: chunks size ((w :: ws).drop size) := by
  rw [chunks]

theorem drop_length_lt (size w : ℕ) [NeZero size] (ws : List ℕ) :
    ((w :: ws).drop size).length < (w :: ws).length := by
  simp only [List.length_drop, List.length_cons]
  have := NeZero.pos size
  omega

theorem flatten_chunks (size : ℕ) [NeZero size] (ws : List ℕ) :
    (chunks size ws).flatten = ws := by
  induction ws using (measure (fun xs : List ℕ => xs.length)).wf.induction with
  | h xs ih =>
    cases xs with
    | nil => simp
    | cons w ws =>
      rw [chunks_cons, List.flatten_cons, ih _ (drop_length_lt size w ws)]
      exact List.take_append_drop _ _

def totals (blocks : List (List ℕ)) : List ℕ := blocks.map List.sum

theorem sum_totals (size : ℕ) [NeZero size] (ws : List ℕ) :
    (totals (chunks size ws)).sum = ws.sum := by
  rw [totals, ← List.sum_flatten, flatten_chunks]

def blockAt (blocks : List (List ℕ)) (i : ℕ) : List ℕ := blocks[i]?.getD []

theorem total_at (blocks : List (List ℕ)) (i : ℕ) :
    (totals blocks)[i]?.getD 0 = (blockAt blocks i).sum := by
  simp only [totals, List.getElem?_map, blockAt]
  cases blocks[i]? <;> rfl

theorem index_lt (blocks : List (List ℕ)) (i : ℕ) (hi : 0 < (blockAt blocks i).sum) :
    i < blocks.length := by
  by_contra h
  simp [blockAt, List.getElem?_eq_none (Nat.le_of_not_gt h)] at hi

theorem ae_pos_block (blocks : List (List ℕ)) :
    ∀ᵐ i ∂WeightedChoice.law (totals blocks), 0 < (blockAt blocks i).sum :=
  (WeightedChoice.ae_pos_weight _).mono fun i hi => by simpa only [total_at] using hi

private theorem weightedSum_append (xs ys : List ℕ) (F : ℕ → ℝ≥0∞) :
    WeightedChoice.weightedSum (xs ++ ys) F = WeightedChoice.weightedSum xs F +
      WeightedChoice.weightedSum ys (fun i => F (xs.length + i)) := by
  induction xs generalizing F with
  | nil => simp [WeightedChoice.weightedSum]
  | cons w xs ih =>
    simp only [List.cons_append, WeightedChoice.weightedSum, List.length_cons]
    rw [ih]
    have hshift : (fun i => F (xs.length + i + 1)) =
        fun i => F (xs.length + 1 + i) := by funext i; congr 1; omega
    rw [hshift, add_assoc]

private theorem block_credit (ws : List ℕ) (F : ℕ → ℝ≥0∞) :
    (ws.sum : ℝ≥0∞) * (∫⁻ i, F i ∂WeightedChoice.law ws) =
      WeightedChoice.weightedSum ws F := by
  rw [WeightedChoice.lintegral_law]
  by_cases hs : ws.sum = 0
  · simp [hs, WeightedChoice.weightedSum_of_sum_zero ws hs]
  · exact ENNReal.mul_div_cancel (by exact_mod_cast hs) (by finiteness)

def blockSum (size : ℕ) : List (List ℕ) → (ℕ → ℝ≥0∞) → ℝ≥0∞
  | [], _ => 0
  | block :: blocks, F => WeightedChoice.weightedSum block F +
      blockSum size blocks (fun i => F (size + i))

def continuation (size : ℕ) (blocks : List (List ℕ)) (F : ℕ → ℝ≥0∞) (i : ℕ) : ℝ≥0∞ :=
  ∫⁻ j, F (i * size + j) ∂WeightedChoice.law (blockAt blocks i)

/-- Conditional normalization cancels each block total, including zero-mass blocks. -/
theorem conditional_blocks (size : ℕ) (blocks : List (List ℕ)) (F : ℕ → ℝ≥0∞) :
    WeightedChoice.weightedSum (totals blocks) (continuation size blocks F) =
      blockSum size blocks F := by
  induction blocks generalizing F with
  | nil => rfl
  | cons block blocks ih =>
    simp only [totals, List.map_cons, WeightedChoice.weightedSum, blockSum]
    have hhead : continuation size (block :: blocks) F 0 =
        ∫⁻ j, F j ∂WeightedChoice.law block := by simp [continuation, blockAt]
    rw [hhead, block_credit]
    have htail : (fun i => continuation size (block :: blocks) F (i + 1)) =
        continuation size blocks (fun j => F (size + j)) := by
      funext i
      simp only [continuation, blockAt, List.getElem?_cons_succ]
      have hindex (j : ℕ) : (i + 1) * size + j = size + (i * size + j) := by
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      simp only [hindex]
    dsimp [totals] at ih
    rw [htail, ih]

/-- Consecutive blocks partition the original categorical expectation. -/
theorem blockSum_chunks (size : ℕ) [NeZero size] (ws : List ℕ) (F : ℕ → ℝ≥0∞) :
    blockSum size (chunks size ws) F = WeightedChoice.weightedSum ws F := by
  induction ws using (measure (fun xs : List ℕ => xs.length)).wf.induction generalizing F with
  | h xs ih =>
    cases xs with
    | nil => simp [blockSum, WeightedChoice.weightedSum]
    | cons w ws =>
      rw [chunks_cons, blockSum, ih _ (drop_length_lt size w ws)]
      by_cases hsize : size ≤ (w :: ws).length
      · have hlen : ((w :: ws).take size).length = size := List.length_take_of_le hsize
        have hsum := weightedSum_append ((w :: ws).take size) ((w :: ws).drop size) F
        rw [List.take_append_drop] at hsum
        simpa only [hlen] using hsum.symm
      · have hshort : (w :: ws).length ≤ size := by omega
        simp [List.take_of_length_le hshort, List.drop_eq_nil_of_le hshort,
          WeightedChoice.weightedSum]

/-- Block choice followed by conditional label choice preserves the canonical law. -/
theorem expectation (size : ℕ) [NeZero size] (ws : List ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ i, continuation size (chunks size ws) F i ∂WeightedChoice.law (totals (chunks size ws)) =
      ∫⁻ i, F i ∂WeightedChoice.law ws := by
  rw [WeightedChoice.lintegral_law, conditional_blocks, blockSum_chunks, sum_totals,
    WeightedChoice.lintegral_law]

end

end SampLib.WeightedBlocks
