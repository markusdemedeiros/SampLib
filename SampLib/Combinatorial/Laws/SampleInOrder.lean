module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Data.List.Sublists
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! # Uniform position subsets in input order

Every selection of positions of the requested size has equal weight. Pascal's rule splits
the first position into its kept and skipped branches.
-/

open Set
open scoped ENNReal

namespace SampLib.SampleInOrder

noncomputable section

variable {α : Type _}
-- Only finitely many lists occur; the output uses the discrete measurable structure.
local instance : MeasurableSpace (List α) := ⊤

open MeasureTheory Measure

/-- Average over the position selections, with multiplicity. -/
def credit (xs : List α) (k : ℕ) (F : List α → ℝ≥0∞) : ℝ≥0∞ :=
  ((xs.sublistsLen k).map F).sum / xs.length.choose k

/-- Uniform position subsets, returned in input order. -/
def law (xs : List α) (k : ℕ) (_hk : k ≤ xs.length) : Measure (List α) :=
  (xs.length.choose k : ℝ≥0∞)⁻¹ • ((xs.sublistsLen k).map dirac).sum

private theorem sum_dirac_univ (ys : List (List α)) :
    (ys.map (dirac : List α → Measure (List α))).sum univ = ys.length := by
  induction ys with
  | nil => simp
  | cons y ys IH => simp [IH, add_comm]

instance (xs : List α) (k : ℕ) (hk : k ≤ xs.length) :
    IsProbabilityMeasure (law xs k hk) where
  measure_univ := by
    simp only [law, Measure.smul_apply, smul_eq_mul, sum_dirac_univ,
      List.length_sublistsLen]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast (Nat.choose_pos hk).ne') (by simp)

private theorem lintegral_sum_dirac (ys : List (List α)) (F : List α → ℝ≥0∞) :
    ∫⁻ y, F y ∂(ys.map dirac).sum = (ys.map F).sum := by
  induction ys with
  | nil => simp
  | cons y ys IH => simp [IH, lintegral_add_measure]

theorem lintegral_law (xs : List α) (k : ℕ) (hk : k ≤ xs.length)
    (F : List α → ℝ≥0∞) : ∫⁻ y, F y ∂law xs k hk = credit xs k F := by
  simp [law, credit, lintegral_smul_measure, lintegral_sum_dirac, div_eq_mul_inv, mul_comm]

@[simp] theorem credit_zero (xs : List α) (F : List α → ℝ≥0∞) :
    credit xs 0 F = F [] := by simp [credit]

private theorem choose_include (n k : ℕ) (hk : k ≤ n) :
    (k + 1 : ℝ≥0∞) / (n + 1) / n.choose k =
      ((n + 1).choose (k + 1) : ℝ≥0∞)⁻¹ := by
  have hn : (n + 1 : NNReal) ≠ 0 := by positivity
  have hc : (n.choose k : NNReal) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have hd : ((n + 1).choose (k + 1) : NNReal) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.succ_le_succ hk)).ne'
  have h : ((k + 1 : ℕ) : NNReal) / (n + 1) / n.choose k =
      ((n + 1).choose (k + 1) : NNReal)⁻¹ := by
    field_simp
    exact_mod_cast (by simpa [mul_comm] using (Nat.add_one_mul_choose_eq n k).symm :
      (k + 1) * (n + 1).choose (k + 1) = (n + 1) * n.choose k)
  simpa only [ENNReal.coe_div hc, ENNReal.coe_div hn, ENNReal.coe_inv hd,
    ENNReal.coe_natCast, ENNReal.coe_add, ENNReal.coe_one, Nat.cast_add, Nat.cast_one]
    using congrArg (fun x : NNReal => (x : ℝ≥0∞)) h

private theorem choose_exclude (n k : ℕ) (hk : k + 1 ≤ n) :
    ((n - k : ℕ) : ℝ≥0∞) / (n + 1) / n.choose (k + 1) =
      ((n + 1).choose (k + 1) : ℝ≥0∞)⁻¹ := by
  have hn : (n + 1 : NNReal) ≠ 0 := by positivity
  have hc : (n.choose (k + 1) : NNReal) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  have hd : ((n + 1).choose (k + 1) : NNReal) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : k + 1 ≤ n + 1)).ne'
  have h : ((n - k : ℕ) : NNReal) / (n + 1) / n.choose (k + 1) =
      ((n + 1).choose (k + 1) : NNReal)⁻¹ := by
    field_simp
    have he := Nat.choose_mul_succ_eq n (k + 1)
    have hs : n + 1 - (k + 1) = n - k := by omega
    rw [hs] at he
    exact_mod_cast (by simpa [mul_comm] using he.symm :
      (n - k) * (n + 1).choose (k + 1) = (n + 1) * n.choose (k + 1))
  simpa only [ENNReal.coe_div hc, ENNReal.coe_div hn, ENNReal.coe_inv hd,
    ENNReal.coe_natCast, ENNReal.coe_add, ENNReal.coe_one, Nat.cast_add, Nat.cast_one]
    using congrArg (fun x : NNReal => (x : ℝ≥0∞)) h

/-- The first position is kept in exactly `k+1` of the `n+1` equally likely ranks. -/
def rankCredit (x : α) (xs : List α) (k : ℕ) (F : List α → ℝ≥0∞)
    (r : ℕ) : ℝ≥0∞ :=
  if r < k + 1 then credit xs k (fun ys => F (x :: ys)) else credit xs (k + 1) F

/-- Pascal's partition of position subsets matches the two continuation branches. -/
theorem expectation (x : α) (xs : List α) (k : ℕ) (hk : k ≤ xs.length)
    (F : List α → ℝ≥0∞) :
    (∑ r ∈ Finset.range (xs.length + 1), rankCredit x xs k F r) /
      (xs.length + 1) = credit (x :: xs) (k + 1) F := by
  have hsum : (∑ r ∈ Finset.range (xs.length + 1), rankCredit x xs k F r) =
      (k + 1 : ℝ≥0∞) * credit xs k (fun ys => F (x :: ys)) +
        ((xs.length - k : ℕ) : ℝ≥0∞) * credit xs (k + 1) F := by
    rw [show xs.length + 1 = (k + 1) + (xs.length - k) by omega,
      Finset.sum_range_add]
    congr 1
    · simp only [rankCredit]
      rw [Finset.sum_congr rfl (fun r hr => ite_eq_left (Finset.mem_range.mp hr))]
      simp [nsmul_eq_mul]
    · simp [rankCredit, Nat.not_lt.mpr (Nat.le_add_right (k + 1) _), nsmul_eq_mul]
  rw [hsum]
  by_cases hfull : k = xs.length
  · subst k
    have hn : (xs.length + 1 : ℝ≥0∞) ≠ 0 := by positivity
    simp only [credit, List.sublistsLen_length, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, Nat.choose_self, Nat.cast_one, div_one,
      Nat.sub_self, Nat.cast_zero, zero_mul, List.length_cons]
    rw [mul_comm, ENNReal.mul_div_cancel_right hn (by simp)]
    simp [List.sublistsLen_of_length_lt (Nat.lt_succ_self xs.length)]
  · have hskip : k + 1 ≤ xs.length := by omega
    calc
      _ = ((k + 1 : ℝ≥0∞) / (xs.length + 1) / xs.length.choose k) *
          ((xs.sublistsLen k).map (fun ys => F (x :: ys))).sum +
          (((xs.length - k : ℕ) : ℝ≥0∞) / (xs.length + 1) /
            xs.length.choose (k + 1)) * ((xs.sublistsLen (k + 1)).map F).sum := by
        simp only [credit, div_eq_mul_inv]
        ring
      _ = _ := by
        rw [choose_include xs.length k hk, choose_exclude xs.length k hskip]
        simp only [credit, List.sublistsLen_succ_cons, List.map_append, List.sum_append,
          List.map_map, Function.comp_def, List.length_cons, div_eq_mul_inv]
        ring

end

end SampLib.SampleInOrder
