import SampLib.Discrete.WeightedChoice

/-! # Integer mass conservation for alias tables -/

open Finset MeasureTheory
open scoped ENNReal

namespace SampLib.AliasMass

noncomputable section

/-- Each column splits `total` integer tickets between its own index and its alias. -/
structure Table (n total : ℕ) where
  threshold : Fin n → ℕ
  target : Fin n → Fin n
  threshold_le : ∀ i, threshold i ≤ total

namespace Table

variable {n total : ℕ}

/-- Tickets arriving at a category through the alias edges. -/
def incoming (t : Table n total) (i : Fin n) : ℕ :=
  ∑ j, if t.target j = i then total - t.threshold j else 0

/-- Own-column tickets together with all incoming alias tickets. -/
def mass (t : Table n total) (i : Fin n) : ℕ := t.threshold i + t.incoming i

/-- A column whose alias is itself needs no second random draw. -/
def columnCredit (t : Table n total) (F : ℕ → ℝ≥0∞) (i : Fin n) : ℝ≥0∞ :=
  if i = t.target i then F i else
    ((t.threshold i : ℝ≥0∞) * F i + (total - t.threshold i : ℕ) * F (t.target i)) / total

end Table

/-- A threshold partitions the integer ticket interval into two consecutive blocks. -/
theorem threshold_sum (total cut : ℕ) (hcut : cut ≤ total) (x y : ℝ≥0∞) :
    ∑ k ∈ range total, (if k < cut then x else y) = cut * x + (total - cut) * y := by
  conv_lhs => rw [← Nat.add_sub_of_le hcut]
  rw [sum_range_add]
  have hleft : (∑ k ∈ range cut, if k < cut then x else y) = cut * x := by
    calc
      _ = ∑ k ∈ range cut, x := sum_congr rfl fun k hk => by
        rw [ite_eq_left (mem_range.mp hk)]
      _ = _ := by simp [nsmul_eq_mul]
  rw [hleft]
  simp [Nat.not_lt.mpr (Nat.le_add_right cut _), nsmul_eq_mul]

private theorem sum_by_target {n : ℕ} (target : Fin n → Fin n)
    (m : Fin n → ℝ≥0∞) (F : Fin n → ℝ≥0∞) :
    ∑ j, m j * F (target j) = ∑ i, (∑ j, if target j = i then m j else 0) * F i := by
  symm
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

/-- Gather column contributions by their output category. No credit is assumed finite. -/
theorem sum_columns {n total : ℕ} (t : Table n total) (F : ℕ → ℝ≥0∞) :
    (∑ j : Fin n, ((t.threshold j : ℝ≥0∞) * F j.val +
      ((total - t.threshold j : ℕ) : ℝ≥0∞) * F (t.target j).val)) =
      ∑ i : Fin n, (t.mass i : ℝ≥0∞) * F i.val := by
  rw [Finset.sum_add_distrib,
    sum_by_target t.target (fun j => ((total - t.threshold j : ℕ) : ℝ≥0∞))
      (fun j => F j.val), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← add_mul]
  congr 1
  simp [Table.mass, Table.incoming]

/-- Express the list's categorical weights using its finite position type. -/
theorem weightedSum_fin (ws : List ℕ) (F : ℕ → ℝ≥0∞) :
    WeightedChoice.weightedSum ws F = ∑ i : Fin ws.length, (ws.get i : ℝ≥0∞) * F i := by
  induction ws generalizing F with
  | nil => simp [WeightedChoice.weightedSum]
  | cons w ws ih => simpa [WeightedChoice.weightedSum, Fin.sum_univ_succ] using
      (congrArg (fun z => (w : ℝ≥0∞) * F 0 + z) (ih (fun i => F (i + 1))))

/-- The identity-alias shortcut has the same expectation as a full ticket draw. -/
theorem columnCredit_eq {n total : ℕ} (t : Table n total) (ht : 0 < total)
    (F : ℕ → ℝ≥0∞) (i : Fin n) :
    t.columnCredit F i =
      ((t.threshold i : ℝ≥0∞) * F i + (total - t.threshold i : ℕ) * F (t.target i)) / total := by
  unfold Table.columnCredit
  split_ifs with hi
  · rw [← hi, ← add_mul, ← Nat.cast_add, Nat.add_sub_of_le (t.threshold_le i), mul_comm]
    exact (ENNReal.mul_div_cancel_right (by positivity) (by simp)).symm
  · rfl

/-- Integer mass conservation identifies the two-stage draw with the categorical law. -/
theorem expectation (ws : List ℕ) (hs : 0 < ws.sum) (t : Table ws.length ws.sum)
    (hmass : ∀ i, t.mass i = ws.length * ws.get i) (F : ℕ → ℝ≥0∞) :
    (∑ i : Fin ws.length, t.columnCredit F i) / ws.length =
      ∫⁻ i, F i ∂WeightedChoice.law ws := by
  have hn : 0 < ws.length := by
    cases ws with
    | nil => simp at hs
    | cons w ws => simp
  simp_rw [columnCredit_eq t hs F]
  rw [← ENNReal.sum_div, sum_columns]
  simp_rw [hmass, Nat.cast_mul, mul_assoc]
  rw [← Finset.mul_sum, WeightedChoice.lintegral_law, weightedSum_fin]
  simp only [div_eq_mul_inv]
  calc
    _ = ((ws.length : ℝ≥0∞)⁻¹ * ws.length) *
        ((∑ i : Fin ws.length, (ws.get i : ℝ≥0∞) * F i) * (ws.sum : ℝ≥0∞)⁻¹) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel (by positivity) (by simp), one_mul]

/-- Extend the column credit beyond the sampled index range by zero. -/
def Table.columnCreditNat {n total : ℕ} (t : Table n total) (F : ℕ → ℝ≥0∞)
    (k : ℕ) : ℝ≥0∞ :=
  if hk : k < n then t.columnCredit F ⟨k, hk⟩ else 0

/-- The integer-uniform primitive and finite-column averages coincide. -/
theorem expectation_range (ws : List ℕ) (hs : 0 < ws.sum) (t : Table ws.length ws.sum)
    (hmass : ∀ i, t.mass i = ws.length * ws.get i) (F : ℕ → ℝ≥0∞) :
    (∑ k ∈ range ws.length, t.columnCreditNat F k) / ws.length =
      ∫⁻ i, F i ∂WeightedChoice.law ws := by
  rw [← Fin.sum_univ_eq_sum_range (t.columnCreditNat F) ws.length]
  simpa only [Table.columnCreditNat, Fin.is_lt, dite_true, Fin.eta] using
    expectation ws hs t hmass F

end

end SampLib.AliasMass
