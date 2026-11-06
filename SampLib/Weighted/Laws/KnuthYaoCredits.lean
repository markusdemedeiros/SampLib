import SampLib.Weighted.Laws.DdgCredits

/-! # Fractional-row expectation conservation for the exact rational matrix -/

open Finset
open scoped NNReal ENNReal

namespace SampLib.KnuthYaoColumns

noncomputable section

variable {n : ℕ}

/-- The unrevealed fraction of one row after `d` bits. -/
def fraction (w : Fin n → ℕ) (T d : ℕ) (i : Fin n) : ℝ≥0 :=
  (remainder w T d i : ℝ≥0) / T

/-- Doubling a fractional row pays one binary digit and retains the next fractional row. -/
theorem fraction_succ (w : Fin n → ℕ) (T : ℕ) (hT : 0 < T) (d : ℕ) (i : Fin n) :
    fraction w T d i = ((column w T d i : ℝ≥0) + fraction w T (d + 1) i) / 2 := by
  apply NNReal.eq
  simp only [fraction, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_add, NNReal.coe_ofNat]
  have h := remainder_succ w T d i
  have hr : (2 : ℝ) * remainder w T d i =
      T * (column w T d i : ℝ) + remainder w T (d + 1) i := by exact_mod_cast h
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hT
  field_simp
  nlinarith

/-- Expected continuation credit remaining in all rows; output credits may be infinite. -/
def rowCredit (w : Fin n → ℕ) (T d : ℕ) (F : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ i, (fraction w T d i : ℝ≥0∞) * F i

/-- The exact column emitted on the next bit extension, in the original category order. -/
def columns (w : Fin n → ℕ) (T d : ℕ) : List ℕ := List.ofFn (column w T d)

theorem weightedSum_ofFn (bs : Fin n → ℕ) (F : ℕ → ℝ≥0∞) :
    WeightedChoice.weightedSum (List.ofFn bs) F = ∑ i, bs i * F i := by
  induction n generalizing F with
  | zero => simp [WeightedChoice.weightedSum]
  | succ n ih =>
    rw [List.ofFn_succ, WeightedChoice.weightedSum, Fin.sum_univ_succ]
    rw [ih]
    rfl

/-- One-bit expectation preservation is just the fractional-row identity summed over categories. -/
theorem row_expectation (w : Fin n → ℕ) (T : ℕ) (hT : 0 < T) (d : ℕ)
    (F : ℕ → ℝ≥0∞) :
    rowCredit w T d F =
      (WeightedChoice.weightedSum (columns w T d) F + rowCredit w T (d + 1) F) / 2 := by
  simp only [rowCredit, columns, weightedSum_ofFn]
  have hterm (i : Fin n) :
      (fraction w T d i : ℝ≥0∞) * F i =
        ((column w T d i : ℝ≥0∞) * F i +
          (fraction w T (d + 1) i : ℝ≥0∞) * F i) * (2 : ℝ≥0∞)⁻¹ := by
    rw [fraction_succ w T hT]
    push_cast
    simp only [div_eq_mul_inv, add_mul]
    ring
  simp_rw [hterm]
  rw [← sum_mul, sum_add_distrib]
  rfl

theorem columns_sum (w : Fin n → ℕ) (T d : ℕ) :
    (columns w T d).sum = ∑ i, column w T d i := by simp [columns, List.sum_ofFn]

/-- Before the first bit, the proper rows are exactly the original probabilities. -/
theorem row_zero (w : Fin n → ℕ) (T : ℕ) (hT : 0 < T) (hproper : ∀ i, w i < T)
    (F : ℕ → ℝ≥0∞) :
    rowCredit w T 0 F = (∑ i, w i * F i) / T := by
  simp only [rowCredit, fraction, remainder, pow_zero, one_mul,
    Nat.mod_eq_of_lt (hproper _)]
  simp only [ENNReal.coe_div (by exact_mod_cast Nat.ne_of_gt hT : (T : ℝ≥0) ≠ 0)]
  push_cast
  simp only [div_eq_mul_inv]
  rw [sum_mul]
  apply sum_congr rfl
  intro i _
  ring

/-- Concrete list weights recover the existing categorical continuation law. -/
theorem row_zero_list (ws : List ℕ) (hT : 0 < ws.sum) (hproper : ∀ i, ws.get i < ws.sum)
    (F : ℕ → ℝ≥0∞) :
    rowCredit ws.get ws.sum 0 F = WeightedChoice.weightedSum ws F / ws.sum := by
  rw [row_zero ws.get ws.sum hT hproper]
  rw [← weightedSum_ofFn, List.ofFn_get]

/-- The on-the-fly source scan computes exactly the next matrix column. -/
theorem columns_list (ws : List ℕ) (T d : ℕ) :
    columns ws.get T d = ws.map (fun w => (w * 2 ^ (d + 1) / T) % 2) := by
  unfold columns column quotient
  conv_rhs => rw [← List.ofFn_get ws, List.map_ofFn]
  congr 1
  funext i
  simp [mul_comm]

/-- One fair bit pays the two exact scan continuations. -/
theorem bit_expectation (w : Fin n → ℕ) (T : ℕ) (F : ℕ → ℝ≥0∞) (h d rank : ℕ) :
    (∑ b ∈ range 2, DdgCredits.scan (columns w T d) (2 * rank + b) F
      (DdgCredits.cutCredit (columns w T) F h (d + 1))) / 2 =
        DdgCredits.cutCredit (columns w T) F (h + 1) d rank := by
  simp [DdgCredits.cutCredit, sum_range_succ]

end

end SampLib.KnuthYaoColumns
