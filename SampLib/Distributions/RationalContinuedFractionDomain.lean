module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Tactic

@[expose] public section

/-! # The first-descent obstruction for unrestricted rational coefficients

For `(b,a,d)=(1,1,2^(i+1))`, every source guard succeeds. The stopping
probabilities along the first descent have total mass at most `5/6`. Consequently
the corresponding independent survival products have a limit at least `1/6`.
This is the probability calculation; operational nontermination requires the
separate identification of the program's first-descent event.
-/

open Finset Filter

namespace SampLib.RationalContinuedFractionDomain

noncomputable section

/-- The first rational coin's stopping probability at source position `i+1`. -/
def stop (i : ℕ) : ℝ := 1 / (1 + (2 : ℝ) ^ (i + 1))

/-- No first-descent stop in the first `n` positions. -/
def survival (n : ℕ) : ℝ := ∏ i ∈ range n, (1 - stop i)

theorem stop_mem (i : ℕ) : 0 ≤ stop i ∧ stop i ≤ 1 := by
  refine ⟨by unfold stop; positivity, ?_⟩
  unfold stop
  exact (div_le_one (by positivity)).mpr (le_add_of_nonneg_right (by positivity))

private theorem tail_bound (i : ℕ) : stop (i + 1) ≤ (1 / 4 : ℝ) * (1 / 2) ^ i := by
  have hp : (0 : ℝ) < 2 ^ (i + 2) := by positivity
  calc
    stop (i + 1) = 1 / (1 + (2 : ℝ) ^ (i + 2)) := by simp [stop, Nat.add_assoc]
    _ ≤ 1 / (2 : ℝ) ^ (i + 2) :=
      one_div_le_one_div_of_le hp (by linarith)
    _ = (1 / 4 : ℝ) * (1 / 2) ^ i := by
      rw [pow_add, div_pow]
      norm_num

theorem stop_sum_le (n : ℕ) : ∑ i ∈ range n, stop i ≤ 5 / 6 := by
  cases n with
  | zero => norm_num
  | succ n =>
    rw [sum_range_succ']
    have h := sum_le_sum (fun i (_ : i ∈ range n) => tail_bound i)
    rw [← mul_sum] at h
    have hg := sum_geometric_two_le n
    norm_num [stop] at h ⊢
    nlinarith

private theorem survival_nonneg (n : ℕ) : 0 ≤ survival n :=
  prod_nonneg (fun i _ => sub_nonneg.mpr (stop_mem i).2)

/-- The finite union bound, proved directly for the independent product. -/
theorem union_bound (n : ℕ) : 1 - ∑ i ∈ range n, stop i ≤ survival n := by
  induction n with
  | zero => norm_num [survival]
  | succ n IH =>
    rw [survival, prod_range_succ]
    rw [sum_range_succ]
    have h := mul_le_mul_of_nonneg_right IH (sub_nonneg.mpr (stop_mem n).2)
    have hs : 0 ≤ ∑ i ∈ range n, stop i := sum_nonneg (fun i _ => (stop_mem i).1)
    change 1 - ((∑ i ∈ range n, stop i) + stop n) ≤ survival n * (1 - stop n)
    nlinarith [mul_nonneg hs (stop_mem n).1]

theorem survival_ge (n : ℕ) : 1 / 6 ≤ survival n := by
  linarith [union_bound n, stop_sum_le n]

private theorem survival_antitone : Antitone survival := by
  apply antitone_nat_of_succ_le
  intro n
  rw [survival, prod_range_succ]
  change survival n * (1 - stop n) ≤ survival n
  nlinarith [mul_nonneg (survival_nonneg n) (stop_mem n).1]

/-- A strictly positive mass survives every finite first-descent prefix. -/
theorem exists_positive_limit : ∃ p : ℝ, 1 / 6 ≤ p ∧ Tendsto survival atTop (nhds p) := by
  refine ⟨⨅ n, survival n, le_ciInf survival_ge, ?_⟩
  exact tendsto_atTop_ciInf survival_antitone ⟨0, by rintro _ ⟨n, rfl⟩; exact survival_nonneg n⟩

end

end SampLib.RationalContinuedFractionDomain
