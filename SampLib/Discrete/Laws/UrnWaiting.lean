import SampLib.Common.Laws.AbsorbingChain
import SampLib.Discrete.Laws.HazardSurvival

/-! # Waiting for the first marked draw of a reinforced urn

Failure reinforces only the unmarked color. The marked-draw hazards dominate a
positive multiple of the harmonic sequence, even when the waiting time has no mean.
-/

open MeasureTheory Measure Filter Finset
open scoped ENNReal Topology

namespace SampLib.UrnWaiting

noncomputable section

/-- The marked-draw hazard after `n` preceding failures. -/
def hazard (a b c n : ℕ) : ℝ := (a : ℝ) / (a + b + n * c)

/-- Continuation probability while waiting for a marked draw. -/
def continuation (a b c n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (1 - hazard a b c n)

theorem hazard_mem (a b c n : ℕ) (ha : 0 < a) : hazard a b c n ∈ Set.Icc 0 1 := by
  have hd : (0 : ℝ) < a + b + n * c := by positivity
  unfold hazard
  exact ⟨by positivity, (div_le_one hd).mpr
    (by nlinarith [show (0 : ℝ) ≤ (n : ℝ) * c by positivity])⟩

/-- A uniform harmonic lower bound suffices for all nonnegative reinforcements. -/
theorem harmonic_lower_bound (a b c n : ℕ) (ha : 0 < a) :
    (a / (a + b + c) : ℝ) * (1 / (n + 1)) ≤ hazard a b c n := by
  have hd : (0 : ℝ) < a + b + n * c := by positivity
  have hsum : (0 : ℝ) < a + b + c := by positivity
  have hn : (0 : ℝ) < n + 1 := by positivity
  rw [hazard, mul_one_div, div_div]
  apply div_le_div_of_nonneg_left (by positivity) hd
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ a + b) (by positivity : (0 : ℝ) ≤ n)]

/-- Every positive marked population eventually produces a marked draw. -/
theorem absorbs (a b c : ℕ) (ha : 0 < a) :
    Tendsto (AbsorbingChain.survival (continuation a b c) 0) atTop (𝓝 0) := by
  apply AbsorbingChain.survival_tendsto_zero_of_hazard_sum
    (fun n => 1 - hazard a b c n)
    (fun n => ⟨sub_nonneg.mpr (hazard_mem a b c n ha).2,
      sub_le_self 1 (hazard_mem a b c n ha).1⟩) 0
  simp only [Nat.zero_add, sub_sub_cancel]
  have hconst : (0 : ℝ) < a / (a + b + c) := by positivity
  apply tendsto_atTop_mono (fun depth => ?_)
    (Real.tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop hconst)
  rw [mul_sum]
  exact sum_le_sum fun n _ => harmonic_lower_bound a b c n ha

/-- Number of unmarked draws preceding the first marked draw. -/
def law (a b c : ℕ) : Measure ℕ := AbsorbingChain.stopLaw (continuation a b c) 0

theorem isProbabilityMeasure_law (a b c : ℕ) (ha : 0 < a) :
    IsProbabilityMeasure (law a b c) :=
  AbsorbingChain.isProbabilityMeasure_stopLaw _
    (fun n => ENNReal.ofReal_le_one.mpr
      (sub_le_self 1 (hazard_mem a b c n ha).1)) 0 (absorbs a b c ha)

/-- A failure is exactly a shift of the unmarked population by the reinforcement. -/
theorem continuation_shift (a b c n : ℕ) :
    continuation a b c (n + 1) = continuation a (b + c) c n := by
  unfold continuation hazard
  congr 2
  push_cast
  ring

private theorem survival_shift (a b c start depth : ℕ) :
    AbsorbingChain.survival (continuation a b c) (start + 1) depth =
      AbsorbingChain.survival (continuation a (b + c) c) start depth := by
  induction depth generalizing start with
  | zero => simp
  | succ depth ih => simp only [AbsorbingChain.survival_succ, continuation_shift, ih]

/-- Shift the waiting mass after one unmarked draw. -/
theorem mass_succ (a b c n : ℕ) :
    AbsorbingChain.mass (continuation a b c) 0 (n + 1) = continuation a b c 0 *
      AbsorbingChain.mass (continuation a (b + c) c) 0 n := by
  rw [AbsorbingChain.mass_succ]
  congr 1
  simp only [AbsorbingChain.mass, Nat.zero_add, survival_shift,
    show 1 + n = n + 1 by omega, continuation_shift]

/-- The first waiting trial separates immediate marking from one reinforced failure. -/
theorem expectation (a b c : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ n, F n ∂law a b c = (1 - continuation a b c 0) * F 0 +
      continuation a b c 0 * ∫⁻ n, F (n + 1) ∂law a (b + c) c := by
  rw [law, law, AbsorbingChain.lintegral_stopLaw, AbsorbingChain.lintegral_stopLaw,
    tsum_eq_zero_add' ENNReal.summable, ← ENNReal.tsum_mul_left]
  simp only [AbsorbingChain.mass_zero, Nat.zero_add]
  congr 1
  apply tsum_congr
  intro n
  rw [mass_succ]
  ring

end

end SampLib.UrnWaiting
