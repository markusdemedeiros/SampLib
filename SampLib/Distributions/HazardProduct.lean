module

public import Mathlib.Analysis.PSeries
public import Mathlib.Tactic

@[expose] public section

/-! # A reciprocal bound on survival products -/

open Filter Finset
open scoped Topology

namespace SampLib.AbsorbingChain

noncomputable section

def realSurvival (q : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 1
  | start, depth + 1 => q start * realSurvival q (start + 1) depth

theorem realSurvival_mem (q : ℕ → ℝ) (hq : ∀ n, q n ∈ Set.Icc 0 1)
    (start depth : ℕ) : realSurvival q start depth ∈ Set.Icc 0 1 := by
  induction depth generalizing start with
  | zero => simp [realSurvival]
  | succ depth ih =>
    exact ⟨mul_nonneg (hq start).1 (ih (start + 1)).1,
      (mul_le_mul_of_nonneg_left (ih (start + 1)).2 (hq start).1).trans
        (by simpa using (hq start).2)⟩

/-- The survival probability is at most the reciprocal cumulative hazard. -/
theorem realSurvival_bound (q : ℕ → ℝ) (hq : ∀ n, q n ∈ Set.Icc 0 1)
    (start depth : ℕ) :
    realSurvival q start depth *
      (1 + ∑ i ∈ range depth, (1 - q (start + i))) ≤ 1 := by
  induction depth generalizing start with
  | zero => simp [realSurvival]
  | succ depth ih =>
    have hs := ih (start + 1)
    obtain ⟨h0, h1⟩ := hq start
    obtain ⟨_, hs1⟩ := realSurvival_mem q hq (start + 1) depth
    have hprod : q start * realSurvival q (start + 1) depth ≤ 1 :=
      (mul_le_mul_of_nonneg_left hs1 h0).trans (by simpa using h1)
    rw [realSurvival, sum_range_succ']
    simp only [Nat.add_zero]
    have hsum : (∑ i ∈ range depth, (1 - q (start + (i + 1)))) =
        ∑ i ∈ range depth, (1 - q (start + 1 + i)) := by
      apply sum_congr rfl
      intro i _
      rw [show start + (i + 1) = start + 1 + i by omega]
    rw [hsum]
    calc
      _ = q start * (realSurvival q (start + 1) depth *
          (1 + ∑ i ∈ range depth, (1 - q (start + 1 + i)))) +
          (1 - q start) * (q start * realSurvival q (start + 1) depth) := by ring
      _ ≤ q start * 1 + (1 - q start) * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hs h0)
          (mul_le_mul_of_nonneg_left hprod (sub_nonneg.mpr h1))
      _ = 1 := by ring

/-- Divergent cumulative hazard implies a vanishing survival product. -/
theorem realSurvival_tendsto_zero_of_hazard_sum (q : ℕ → ℝ)
    (hq : ∀ n, q n ∈ Set.Icc 0 1) (start : ℕ)
    (hazards : Tendsto (fun depth => ∑ i ∈ range depth, (1 - q (start + i)))
      atTop atTop) : Tendsto (realSurvival q start) atTop (𝓝 0) := by
  have hden : Tendsto
      (fun depth => 1 + ∑ i ∈ range depth, (1 - q (start + i))) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_add_of_nonneg_left zero_le_one) hazards
  apply squeeze_zero (fun depth => (realSurvival_mem q hq start depth).1)
    (fun depth => ?_) hden.inv_tendsto_atTop
  have hpos : 0 < 1 + ∑ i ∈ range depth, (1 - q (start + i)) := by
    have hsum : 0 ≤ ∑ i ∈ range depth, (1 - q (start + i)) :=
      sum_nonneg fun i _ => sub_nonneg.mpr (hq _).2
    positivity
  simpa only [one_div, Pi.inv_apply] using (le_div_iff₀ hpos).mpr
    (realSurvival_bound q hq start depth)

end

end SampLib.AbsorbingChain
