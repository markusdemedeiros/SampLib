module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

/-! # The extinction bound for critical fair binary branching

A node either stops or has two children, each with probability one half.
The depth-truncated survival probabilities tend to zero, even though no uniform
geometric contraction is available. The explicit bound is useful in CTE proofs
of nested fair-coin recursions.
-/

@[expose] public section

namespace SampLib.CriticalBranching

noncomputable section

open Filter

/-- Probability that the fair binary tree reaches beyond the given depth. -/
def survival : ℕ → ℝ
  | 0 => 1
  | n + 1 => survival n - survival n ^ 2 / 2

theorem survival_mem (n : ℕ) : 0 ≤ survival n ∧ survival n ≤ 1 := by
  induction n with
  | zero => norm_num [survival]
  | succ n IH =>
    dsimp only [survival]
    constructor <;> nlinarith [sq_nonneg (survival n), mul_nonneg IH.1 (sub_nonneg.mpr IH.2)]

/-- Critical branching has a polynomial, rather than geometric, extinction bound. -/
theorem survival_le (n : ℕ) : survival n ≤ 2 / ((n : ℝ) + 2) := by
  induction n with
  | zero => norm_num [survival]
  | succ n IH =>
    have hs := survival_mem n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hb : 2 / ((n : ℝ) + 2) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    have hstep : survival n - survival n ^ 2 / 2 ≤
        2 / ((n : ℝ) + 2) - (2 / ((n : ℝ) + 2)) ^ 2 / 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr IH)
        (show 0 ≤ 2 - survival n - 2 / ((n : ℝ) + 2) by linarith)]
    change survival n - survival n ^ 2 / 2 ≤ 2 / (((n + 1 : ℕ) : ℝ) + 2)
    refine hstep.trans ?_
    push_cast
    apply (sub_le_iff_le_add).mpr
    field_simp
    nlinarith

/-- The unresolved probability vanishes without any finite expected-time hypothesis. -/
theorem survival_tendsto : Filter.Tendsto survival Filter.atTop (nhds 0) := by
  apply squeeze_zero (fun n => (survival_mem n).1) survival_le
  have hn : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 2) Filter.atTop Filter.atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 2)⁻¹) atTop (nhds (2 * 0)) :=
    tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hn)
  simpa only [div_eq_mul_inv, mul_zero] using ht

end

end SampLib.CriticalBranching
