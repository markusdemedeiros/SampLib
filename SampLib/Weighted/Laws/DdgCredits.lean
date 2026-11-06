import SampLib.Weighted.Laws.KnuthYaoColumns

/-! # Finite-horizon credits for a binary distribution-generating graph

A column consumes its leaves in label order and retains the remaining ranks.
At a finite cutoff, every surviving rank receives one error credit. Summing
those credits exposes the live-rank bound, without requiring finite mean runtime.
-/

open Finset
open scoped ENNReal

namespace SampLib.DdgCredits

noncomputable section

/-- Scan the leaves before handing the remaining distance to the continuation. -/
def scan : List ℕ → ℕ → (ℕ → ℝ≥0∞) → (ℕ → ℝ≥0∞) → ℝ≥0∞
  | [], d, _, next => next d
  | b :: bs, d, F, next =>
      if d < b then F 0 else scan bs (d - b) (fun i => F (i + 1)) next

/-- A column partitions all ranks into its leaves and its surviving ranks. -/
theorem scan_partition (bs : List ℕ) (a : ℕ) (F next : ℕ → ℝ≥0∞) :
    (∑ d ∈ range (bs.sum + a), scan bs d F next) =
      WeightedChoice.weightedSum bs F + ∑ d ∈ range a, next d := by
  induction bs generalizing F with
  | nil => simp [scan, WeightedChoice.weightedSum]
  | cons b bs ih =>
    rw [List.sum_cons, add_assoc, sum_range_add]
    have hfirst : (∑ d ∈ range b, scan (b :: bs) d F next) = b * F 0 := by
      simp only [scan]
      rw [sum_congr rfl (fun d hd => ite_eq_left (mem_range.mp hd))]
      simp [nsmul_eq_mul]
    have hrest : (∑ d ∈ range (bs.sum + a), scan (b :: bs) (b + d) F next) =
        ∑ d ∈ range (bs.sum + a), scan bs d (fun i => F (i + 1)) next := by
      apply sum_congr rfl
      intro d _
      simp only [scan, Nat.not_lt.mpr (Nat.le_add_right b d), ite_false,
        Nat.add_sub_cancel_left]
    rw [hfirst, hrest, ih]
    simp only [WeightedChoice.weightedSum, add_assoc]

/-- Pairing the two children enumerates precisely the doubled range. -/
theorem sum_children (a : ℕ) (f : ℕ → ℝ≥0∞) :
    (∑ d ∈ range a, (f (2 * d) + f (2 * d + 1))) = ∑ d ∈ range (2 * a), f d := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [sum_range_succ, ih, show 2 * (a + 1) = 2 * a + 2 by omega, sum_range_add]
    simp only [sum_range_succ, sum_range_zero, zero_add, add_zero]

/-- Truncated execution pays one credit on every path still alive at the cutoff. -/
def cutCredit (columns : ℕ → List ℕ) (F : ℕ → ℝ≥0∞) : ℕ → ℕ → ℕ → ℝ≥0∞
  | 0, _, _ => 1
  | h + 1, d, rank =>
      (scan (columns d) (2 * rank) F (cutCredit columns F h (d + 1)) +
        scan (columns d) (2 * rank + 1) F (cutCredit columns F h (d + 1))) / 2

/-- Expected credit is conserved by one fair-bit extension and one column scan. -/
theorem aggregate_succ (columns : ℕ → List ℕ) (alive : ℕ → ℕ)
    (width : ∀ d, 2 * alive d = (columns d).sum + alive (d + 1))
    (F : ℕ → ℝ≥0∞) (h d : ℕ) :
    (∑ rank ∈ range (alive d), cutCredit columns F (h + 1) d rank) =
      (WeightedChoice.weightedSum (columns d) F +
        ∑ rank ∈ range (alive (d + 1)), cutCredit columns F h (d + 1) rank) / 2 := by
  simp only [cutCredit, div_eq_mul_inv, ← sum_mul]
  rw [sum_children (alive d) (fun rank =>
    scan (columns d) rank F (cutCredit columns F h (d + 1))), width, scan_partition]

/-- A uniform live-rank bound controls the cutoff independently of the credit's size. -/
theorem aggregate_le (columns : ℕ → List ℕ) (alive : ℕ → ℕ)
    (width : ∀ d, 2 * alive d = (columns d).sum + alive (d + 1))
    (F : ℕ → ℝ≥0∞) (row : ℕ → ℝ≥0∞)
    (conservation : ∀ d, row d = (WeightedChoice.weightedSum (columns d) F + row (d + 1)) / 2)
    (bound : ℕ) (bounded : ∀ d, alive d ≤ bound) (h d : ℕ) :
    (∑ rank ∈ range (alive d), cutCredit columns F h d rank) ≤
      row d + bound * (1 / 2 : ℝ≥0∞) ^ h := by
  induction h generalizing d with
  | zero =>
    simp only [cutCredit, sum_const, card_range, nsmul_eq_mul, mul_one, pow_zero]
    exact (by exact_mod_cast bounded d : (alive d : ℝ≥0∞) ≤ bound).trans
      (le_add_left le_rfl)
  | succ h ih =>
    rw [aggregate_succ columns alive width]
    calc
      _ ≤ (WeightedChoice.weightedSum (columns d) F +
          (row (d + 1) + bound * (1 / 2 : ℝ≥0∞) ^ h)) / 2 := by gcongr; exact ih (d + 1)
      _ = row d + bound * (1 / 2 : ℝ≥0∞) ^ (h + 1) := by
        rw [conservation d]
        simp only [pow_succ, div_eq_mul_inv, one_mul]
        ring

end

end SampLib.DdgCredits
