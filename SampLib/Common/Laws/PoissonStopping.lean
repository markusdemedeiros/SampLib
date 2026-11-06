module

public import SampLib.Common.Laws.PoissonMeasure
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

@[expose] public section

/-! # Stopping masses of the Duchon–Duvignau tree

Binomial sums count the live predecessors of a node. The odd-factorial stopping weights
sum to the Poisson mass at each output.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.PoissonTree

noncomputable section

open Finset

/-- Hockey-stick summation, including indices below the lower argument. -/
theorem sum_choose (n k : ℕ) :
    ∑ i ∈ range n, i.choose k = n.choose (k + 1) := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [sum_range_succ, IH, Nat.choose_succ_succ']
    exact Nat.add_comm _ _

/-- Sum the possible largest omitted labels in an `m`-element complement. -/
theorem sum_largest_label (n m : ℕ) (hm : 0 < m) :
    ∑ i ∈ range n, (i + 1) * i.choose (m - 1) =
      m * (n + 1).choose (m + 1) := by
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  simp_rw [Nat.add_one_mul_choose_eq, hm', mul_comm _ m]
  rw [← mul_sum]
  congr 1
  have h := sum_choose (n + 1) m
  rw [sum_range_succ'] at h
  simpa [Nat.choose_eq_zero_of_lt hm] using h

/-- A second hockey-stick sum counts predecessors whose last omitted label increases. -/
theorem sum_live_predecessors (n m : ℕ) (hm : 0 < m) :
    ∑ i ∈ range n, (n - (i + 1)) * i.choose (m - 1) = n.choose (m + 1) := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [sum_range_succ]
    simp only [Nat.add_sub_add_right, Nat.sub_self, zero_mul, add_zero]
    have hsplit : (∑ i ∈ range n, (n - i) * i.choose (m - 1)) =
        (∑ i ∈ range n, (n - (i + 1)) * i.choose (m - 1)) +
          ∑ i ∈ range n, i.choose (m - 1) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro i hi
      have hsub : n - i = n - (i + 1) + 1 := by have := mem_range.mp hi; omega
      rw [hsub, add_mul, one_mul]
    rw [hsplit, IH, sum_choose, Nat.sub_add_cancel hm, Nat.choose_succ_succ']
    exact Nat.add_comm _ _

/-- The parity-subset stopping weights are the difference of the even and odd
exponential series. -/
theorem hasSum_stopping_weights :
    HasSum (fun k : ℕ => ((2 * k : ℕ) : ℝ) / (2 * k + 1).factorial)
      (Real.exp (-1)) := by
  have h := (Real.hasSum_cosh (1 : ℝ)).sub (Real.hasSum_sinh (1 : ℝ))
  simp only [one_pow, Real.cosh_sub_sinh] at h
  convert h using 1
  ext k
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- After fixing the returned cardinality, the stopping weights have Poisson mass. -/
theorem hasSum_stopping_mass (r : ℕ) :
    HasSum (fun k : ℕ => ((2 * k : ℕ) : ℝ) /
      ((r.factorial * (2 * k + 1).factorial : ℕ) : ℝ))
      (Real.exp (-1) / r.factorial) := by
  convert hasSum_stopping_weights.div_const (r.factorial : ℝ) using 1
  ext k
  rw [div_div]
  push_cast
  congr 1
  ring

theorem tsum_stopping_mass (r : ℕ) :
    (∑' k : ℕ, ((2 * k : ℕ) : ℝ≥0∞) /
      ((r.factorial * (2 * k + 1).factorial : ℕ) : ℝ≥0∞)) =
      ProbabilityTheory.poissonMeasure 1 {r} := by
  rw [ProbabilityTheory.poissonMeasure_singleton]
  simp only [NNReal.coe_one, one_pow, mul_one]
  have h := hasSum_stopping_mass r
  calc
    _ = ∑' k : ℕ, ENNReal.ofReal (((2 * k : ℕ) : ℝ) /
        ((r.factorial * (2 * k + 1).factorial : ℕ) : ℝ)) := by
      apply tsum_congr
      intro k
      rw [ENNReal.ofReal_div_of_pos (by positivity)]
      simp only [ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal (∑' k : ℕ, ((2 * k : ℕ) : ℝ) /
        ((r.factorial * (2 * k + 1).factorial : ℕ) : ℝ)) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) h.summable).symm
    _ = _ := by rw [h.tsum_eq]

end

end SampLib.PoissonTree
