module

public import SampLib.Distributions.LatentReal.IntervalLimits
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! # Canonical dyadic enclosures of a real value -/

open scoped Topology

namespace SampLib.LatentUniform

open LatentReal

noncomputable section

/-- The canonical dyadic cell at precision `n`, defined for every real value. -/
def dyadicInterval (n : ℕ) (x : ℝ) : RationalInterval where
  lower := ⌊x * 2 ^ n⌋
  upper := ⌊x * 2 ^ n⌋ + 1
  denominator := 2 ^ n
  denominator_pos := pow_pos (by norm_num) _
  lower_le_upper := by omega

theorem dyadicInterval_contains (n : ℕ) (x : ℝ) : (dyadicInterval n x).Contains x := by
  have hD : (0 : ℝ) < 2 ^ n := by positivity
  simp only [RationalInterval.Contains, RationalInterval.lowerReal,
    RationalInterval.upperReal, dyadicInterval, Int.cast_pow, Int.cast_ofNat, Int.cast_add,
    Int.cast_one]
  exact ⟨(div_le_iff₀ hD).mpr (Int.floor_le _),
    (le_div_iff₀ hD).mpr (Int.lt_floor_add_one _).le⟩

theorem dyadicInterval_width (n : ℕ) (x : ℝ) :
    (dyadicInterval n x).width = (2 ^ n : ℝ)⁻¹ := by
  simp only [RationalInterval.width, RationalInterval.lowerReal,
    RationalInterval.upperReal, dyadicInterval, Int.cast_pow, Int.cast_ofNat, Int.cast_add,
    Int.cast_one]
  rw [add_div, add_sub_cancel_left, one_div]

/-- Canonical cells enclose the value and shrink at the binary rate. -/
theorem dyadicInterval_approximates (x : ℝ) :
    RationalInterval.Approximates (fun n => dyadicInterval n x) x := by
  refine ⟨fun n => dyadicInterval_contains n x, ?_⟩
  simp only [dyadicInterval_width]
  exact tendsto_inv_atTop_zero.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

end

end SampLib.LatentUniform
