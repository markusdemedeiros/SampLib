module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section

/-! # Rescaling a shadow interval under reverse conditioning

The previous thresholds need not enclose a fixed target pointwise. Their
conditional means are the old Bernstein coefficients. Rescaling the whole
threshold width transports these two means to the new coefficients.
-/

open Finset

namespace SampLib.EnvelopeFactory

noncomputable section

def lowerUpdate (L U a b l : ℝ) : ℝ := L + (l - a) * (U - L) / (b - a)
def upperUpdate (L U a b u : ℝ) : ℝ := U - (b - u) * (U - L) / (b - a)

theorem updated_width (L U a b l u : ℝ) (hab : a ≠ b) :
    upperUpdate L U a b u - lowerUpdate L U a b l =
      (u - l) * (U - L) / (b - a) := by
  unfold lowerUpdate upperUpdate
  field_simp [sub_ne_zero.mpr (Ne.symm hab)]
  ring

/-- Degree-elevation consistency makes every shadow interval shrink pointwise. -/
theorem updates_nested (L U a b l u : ℝ) (hLU : L ≤ U)
    (hal : a ≤ l) (hlu : l ≤ u) (hub : u ≤ b) :
    L ≤ lowerUpdate L U a b l ∧
      lowerUpdate L U a b l ≤ upperUpdate L U a b u ∧
      upperUpdate L U a b u ≤ U := by
  by_cases hab : a = b
  · subst b
    simp only [lowerUpdate, upperUpdate, sub_self, div_zero, add_zero, sub_zero]
    exact ⟨le_rfl, hLU, le_rfl⟩
  · have hba : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne (hal.trans (hlu.trans hub)) hab)
    have hwidth : 0 ≤ U - L := sub_nonneg.mpr hLU
    refine ⟨?_, ?_, ?_⟩
    · exact le_add_of_nonneg_right (div_nonneg (mul_nonneg (sub_nonneg.mpr hal) hwidth) hba.le)
    · apply sub_nonneg.mp
      rw [updated_width L U a b l u hab]
      exact div_nonneg (mul_nonneg (sub_nonneg.mpr hlu) hwidth) hba.le
    · exact sub_le_self _ (div_nonneg (mul_nonneg (sub_nonneg.mpr hub) hwidth) hba.le)

section finite

variable {ι : Type} [Fintype ι]

def mean (w f : ι → ℝ) : ℝ := ∑ i, w i * f i

theorem mean_lowerUpdate (w L U : ι → ℝ) (a b l : ℝ) :
    mean w (fun i => lowerUpdate (L i) (U i) a b l) =
      mean w L + (l - a) / (b - a) * (mean w U - mean w L) := by
  unfold mean
  rw [← sum_sub_distrib, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  unfold lowerUpdate
  ring

theorem mean_upperUpdate (w L U : ι → ℝ) (a b u : ℝ) :
    mean w (fun i => upperUpdate (L i) (U i) a b u) =
      mean w U - (b - u) / (b - a) * (mean w U - mean w L) := by
  unfold mean
  rw [← sum_sub_distrib, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  unfold upperUpdate
  ring

/-- The one expectation-preservation argument, including a zero old mean width. -/
theorem rescaling_preserves_means (w L U : ι → ℝ) (a b l u : ℝ)
    (hL : mean w L = a) (hU : mean w U = b)
    (hal : a ≤ l) (hlu : l ≤ u) (hub : u ≤ b) :
    mean w (fun i => lowerUpdate (L i) (U i) a b l) = l ∧
      mean w (fun i => upperUpdate (L i) (U i) a b u) = u := by
  rw [mean_lowerUpdate, mean_upperUpdate, hL, hU]
  by_cases hab : a = b
  · have hl : l = a := by linarith
    have hu : u = a := by linarith
    simp [hab, hl, hu]
  · have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    constructor <;> field_simp [hba] <;> ring

/-- A reachable positive-width history forces a positive conditional mean width. -/
theorem mean_width_pos (w L U : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hLU : ∀ i, L i ≤ U i) (i : ι) (hwi : 0 < w i) (hi : L i < U i) :
    0 < mean w U - mean w L := by
  have hterm : 0 < w i * (U i - L i) := mul_pos hwi (sub_pos.mpr hi)
  have hle := single_le_sum (fun j (_ : j ∈ (univ : Finset ι)) =>
    mul_nonneg (hw j) (sub_nonneg.mpr (hLU j))) (mem_univ i)
  have hsum : (∑ j, w j * (U j - L j)) = mean w U - mean w L := by
    simp only [mean, mul_sub, sum_sub_distrib]
  rw [hsum] at hle
  exact hterm.trans_le hle

/-- Zero average width collapses every history with positive conditional weight. -/
theorem width_zero_of_mean_eq (w L U : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hLU : ∀ i, L i ≤ U i) (hmean : mean w L = mean w U)
    (i : ι) (hwi : 0 < w i) : L i = U i := by
  by_contra hne
  have hi : L i < U i := lt_of_le_of_ne (hLU i) hne
  have hpos := mean_width_pos w L U hw hLU i hwi hi
  linarith

end finite

end

end SampLib.EnvelopeFactory
