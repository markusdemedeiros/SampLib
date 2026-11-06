module

public import SampLib.Common.Laws.ExponentialFactory
public import Mathlib.Data.List.Pairwise
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

/-! # Power densities for maxima of independent uniforms

The density `(n+1)t^n` integrates to `t^(n+1)`. Its CDF therefore matches
that of the maximum of `n+1` independent unit uniforms.
-/

open Set MeasureTheory Real ProbLang
open ENNReal (ofReal)
open LawfulProbLangℝ (unifUnit)
open scoped ENNReal

namespace SampLib.MaximumUniform

noncomputable section

def density (n : ℕ) (t : ℝ) : ℝ≥0∞ := ofReal (((n + 1 : ℕ) : ℝ) * t ^ n)

def law (n : ℕ) : Measure ℝ := unifUnit.withDensity (density n)

theorem measurable_density (n : ℕ) : Measurable (density n) := by
  unfold density
  fun_prop

private theorem lower_window (t : ℝ) : Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 (min t 1) := by
  ext y
  change (y ≤ t ∧ 0 ≤ y ∧ y ≤ 1) ↔ 0 ≤ y ∧ y ≤ min t 1
  exact ⟨fun h => ⟨h.2.1, le_min h.1 h.2.2⟩,
    fun h => ⟨(le_min_iff.mp h.2).1, h.1, (le_min_iff.mp h.2).2⟩⟩

theorem unit_apply_Iic (t : ℝ) : (unifUnit : Measure ℝ) (Iic t) = ofReal (min t 1) := by
  change volume.restrict (Icc (0 : ℝ) 1) (Iic t) = _
  rw [Measure.restrict_apply measurableSet_Iic, lower_window, Real.volume_Icc, sub_zero]

/-- The polynomial density is the derivative of the power CDF. -/
theorem integral_density (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ∫⁻ t in Icc (0 : ℝ) x, density n t = ofReal (x ^ (n + 1)) := by
  unfold density
  rw [ProbLang.TotalEris.Examples.lintegral_ofReal_Icc hx (by fun_prop)
    (fun t ht => mul_nonneg (by positivity) (pow_nonneg ht.1 _))]
  congr 1
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp only [zero_pow (by omega : n + 1 ≠ 0), sub_zero, Nat.cast_add, Nat.cast_one]
  field_simp

instance (n : ℕ) : IsProbabilityMeasure (law n) where
  measure_univ := by
    rw [law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    change (∫⁻ t in Icc (0 : ℝ) 1, density n t) = 1
    rw [integral_density n 1 zero_le_one]
    simp

instance (n : ℕ) : NullSingletonClass (law n) := by
  change NullSingletonClass ((volume.restrict (Icc (0 : ℝ) 1)).withDensity (density n))
  infer_instance

/-- The clipped unit CDF raised to the number of samples. -/
theorem law_apply_Iic (n : ℕ) (t : ℝ) : law n (Iic t) = (unifUnit (Iic t)) ^ (n + 1) := by
  rw [law, withDensity_apply _ measurableSet_Iic]
  change (∫⁻ y, density n y ∂(volume.restrict (Icc (0 : ℝ) 1)).restrict (Iic t)) = _
  rw [Measure.restrict_restrict measurableSet_Iic, lower_window, unit_apply_Iic]
  by_cases ht : 0 ≤ t
  · rw [integral_density n (min t 1) (le_min ht zero_le_one),
      ENNReal.ofReal_pow (le_min ht zero_le_one)]
  · have hneg : min t 1 < 0 := (min_le_left t 1).trans_lt (lt_of_not_ge ht)
    rw [Icc_eq_empty_of_lt hneg, Measure.restrict_empty, lintegral_zero_measure,
      ENNReal.ofReal_eq_zero.mpr hneg.le, zero_pow (by omega)]

/-- Weighting never moves the proposal outside the unit interval. -/
theorem ae_mem_unit (n : ℕ) : ∀ᵐ t ∂law n, t ∈ Icc (0 : ℝ) 1 := by
  change ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)).withDensity (density n), t ∈ Icc 0 1
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem measurableSet_Icc)

end

end SampLib.MaximumUniform
