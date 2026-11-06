module

public import Metrology.TotalEris.Examples.Samplers.HalfBernNegExp
public import Mathlib.MeasureTheory.Constructions.UnitInterval

@[expose] public section

/-! # Exponential kernels for decreasing-uniform factories

The fundamental theorem of calculus evaluates the continuation masses without
division by the input bias, so the deterministic endpoints require no exceptions.
-/

open Set MeasureTheory Real
open ENNReal (ofReal)
open ProbLang
open LawfulProbLangℝ (unifUnit)
open scoped ENNReal NNReal

namespace SampLib.ExponentialFactory

noncomputable section

theorem integral_mul_exp (a x : ℝ) :
    ∫ y in (0 : ℝ)..x, a * exp (a * y) = exp (a * x) - 1 := by
  have hd (y : ℝ) : HasDerivAt (fun z => exp (a * z)) (a * exp (a * y)) y := by
    simpa only [Function.comp_def, mul_one, mul_comm] using
      (Real.hasDerivAt_exp (a * y)).comp y ((hasDerivAt_id y).const_mul a)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)
    (Continuous.intervalIntegrable (by fun_prop) 0 x)
  simpa only [mul_zero, exp_zero] using h

/-- The probability of retaining the current parity below threshold `x`. -/
def decay (p : unitInterval) (x : ℝ) : unitInterval :=
  ⟨exp (-(p : ℝ) * max 0 x), (exp_pos _).le,
    exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr p.2.1) (le_max_left _ _))⟩

@[simp] theorem decay_coe (p : unitInterval) (x : ℝ) (hx : 0 ≤ x) :
    (decay p x : ℝ) = exp (-(p : ℝ) * x) := by simp [decay, max_eq_right hx]

theorem measurable_decay (p : unitInterval) : Measurable (decay p) :=
  (by fun_prop : Measurable (fun x : ℝ => exp (-(p : ℝ) * max 0 x))).subtype_mk

/-- Probability of reversing parity after the next uniform draw. -/
def flipBias (p : unitInterval) (x y : ℝ) : unitInterval :=
  if y < x then p * decay p y else 0

theorem measurable_flipBias (p : unitInterval) (x : ℝ) : Measurable (flipBias p x) :=
  Measurable.ite measurableSet_Iio (measurable_const.mul (measurable_decay p)) measurable_const

private theorem lower_window (x : ℝ) (hx : x ≤ 1) :
    Iio x ∩ Icc (0 : ℝ) 1 = Ico 0 x := by
  ext y
  simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
  exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.le.trans hx⟩⟩

theorem decay_integral (p : unitInterval) (x : ℝ) (hx : 0 ≤ x) :
    ∫⁻ y in Icc (0 : ℝ) x, ofReal ((p : ℝ) * exp (-(p : ℝ) * y)) =
      ofReal (1 - exp (-(p : ℝ) * x)) := by
  rw [ProbLang.TotalEris.Examples.lintegral_ofReal_Icc hx (by fun_prop)
    (fun y _ => mul_nonneg p.2.1 (exp_pos _).le)]
  have h := integral_mul_exp (-(p : ℝ)) x
  simp only [neg_mul] at h ⊢
  rw [intervalIntegral.integral_neg] at h
  congr 1
  linarith

/-- The first-step parity-reversal mass is the integral of `p exp(-py)`. -/
theorem flip_mass (p : unitInterval) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    ∫⁻ y, ofReal (flipBias p x y : ℝ) ∂unifUnit = ofReal (1 - (decay p x : ℝ)) := by
  have hfun : (fun y => ofReal (flipBias p x y : ℝ)) =
      (Iio x).indicator (fun y => ofReal ((p : ℝ) * (decay p y : ℝ))) := by
    funext y
    by_cases h : y < x <;> simp [flipBias, h]
  rw [hfun]
  change (∫⁻ y, _ ∂volume.restrict (Icc (0 : ℝ) 1)) = _
  rw [ProbLang.TotalEris.Examples.lintegral_indicator_restrict measurableSet_Iio,
    lower_window x hx.2, restrict_Ico_eq_restrict_Icc]
  rw [setLIntegral_congr_fun measurableSet_Icc
    (fun y hy => by rw [decay_coe p y hy.1]), decay_integral p x hx.1,
    decay_coe p x hx.1]

/-- The continuation event has probability `p*x`. -/
theorem continuation_mass (p : unitInterval) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    ∫⁻ y, (if y < x then ofReal (p : ℝ) else 0) ∂unifUnit = ofReal ((p : ℝ) * x) := by
  change (∫⁻ y, _ ∂volume.restrict (Icc (0 : ℝ) 1)) = _
  have hfun : (fun y => if y < x then ofReal (p : ℝ) else 0) =
      (Iio x).indicator (fun _ => ofReal (p : ℝ)) := rfl
  rw [hfun, ProbLang.TotalEris.Examples.lintegral_indicator_restrict measurableSet_Iio,
    lower_window x hx.2, setLIntegral_const, Real.volume_Ico, sub_zero,
    ← ENNReal.ofReal_mul p.2.1]

/-- The exponential tangent inequality bounds `(1-p) exp(p)` by one. -/
theorem growth_le_one (p : unitInterval) : (1 - (p : ℝ)) * exp (p : ℝ) ≤ 1 := by
  calc
    _ ≤ exp (-(p : ℝ)) * exp (p : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (-(p : ℝ))])
        (exp_pos _).le
    _ = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]

/-- The successful-exit probability for a sorted-uniform threshold. -/
def growth (p : unitInterval) (x : ℝ) : unitInterval :=
  ⟨(1 - (p : ℝ)) * exp ((p : ℝ) * min 1 (max 0 x)),
    mul_nonneg (sub_nonneg.mpr p.2.2) (exp_pos _).le,
    (mul_le_mul_of_nonneg_left (exp_le_exp.mpr
      (mul_le_of_le_one_right p.2.1 (min_le_left _ _)))
      (sub_nonneg.mpr p.2.2)).trans (growth_le_one p)⟩

@[simp] theorem growth_coe (p : unitInterval) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    (growth p x : ℝ) = (1 - (p : ℝ)) * exp ((p : ℝ) * x) := by
  simp [growth, max_eq_right hx.1, min_eq_right hx.2]

theorem measurable_growth (p : unitInterval) : Measurable (growth p) :=
  (by fun_prop : Measurable (fun x : ℝ =>
    (1 - (p : ℝ)) * exp ((p : ℝ) * min 1 (max 0 x)))).subtype_mk

def growthWindow (p : unitInterval) (x y : ℝ) : unitInterval :=
  if x < y then 0 else growth p y

def growthStep (p : unitInterval) (x y : ℝ) : unitInterval :=
  unitInterval.symm (p * unitInterval.symm (growthWindow p x y))

theorem measurable_growthWindow (p : unitInterval) (x : ℝ) :
    Measurable (growthWindow p x) :=
  Measurable.ite measurableSet_Ioi measurable_const (measurable_growth p)

theorem measurable_growthStep (p : unitInterval) (x : ℝ) :
    Measurable (growthStep p x) :=
  unitInterval.measurable_symm.comp (measurable_const.mul
    (unitInterval.measurable_symm.comp (measurable_growthWindow p x)))

private theorem upper_window (x : ℝ) (hx : x ≤ 1) :
    Iic x ∩ Icc (0 : ℝ) 1 = Icc 0 x := by
  ext y
  simp only [mem_inter_iff, mem_Iic, mem_Icc]
  exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans hx⟩⟩

private theorem growth_window_mass (p : unitInterval) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    ∫⁻ y, ofReal ((p : ℝ) * (growthWindow p x y : ℝ)) ∂unifUnit =
      ofReal ((1 - (p : ℝ)) * (exp ((p : ℝ) * x) - 1)) := by
  have hfun : (fun y => ofReal ((p : ℝ) * (growthWindow p x y : ℝ))) =
      (Iic x).indicator (fun y => ofReal ((p : ℝ) * (growth p y : ℝ))) := by
    funext y
    by_cases h : x < y <;> simp [growthWindow, h, indicator_apply, not_le]
  rw [hfun]
  change (∫⁻ y, _ ∂volume.restrict (Icc (0 : ℝ) 1)) = _
  rw [ProbLang.TotalEris.Examples.lintegral_indicator_restrict measurableSet_Iic,
    upper_window x hx.2]
  rw [setLIntegral_congr_fun measurableSet_Icc
    (fun y hy => by rw [growth_coe p y ⟨hy.1, hy.2.trans hx.2⟩])]
  rw [ProbLang.TotalEris.Examples.lintegral_ofReal_Icc hx.1 (by fun_prop)
    (fun y _ => mul_nonneg p.2.1 (mul_nonneg (sub_nonneg.mpr p.2.2) (exp_pos _).le))]
  congr 1
  calc
    _ = (1 - (p : ℝ)) * ∫ y in (0 : ℝ)..x, (p : ℝ) * exp ((p : ℝ) * y) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext y
      ring
    _ = _ := by rw [integral_mul_exp]

/-- The sorted-uniform recurrence integrates to `(1-p) exp(px)`. -/
theorem growth_step_mass (p : unitInterval) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    ∫⁻ y, ofReal (growthStep p x y : ℝ) ∂unifUnit = ofReal (growth p x : ℝ) := by
  have hpoint (y : ℝ) : ofReal (growthStep p x y : ℝ) =
      ofReal (1 - (p : ℝ)) + ofReal ((p : ℝ) * (growthWindow p x y : ℝ)) := by
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr p.2.2)
      (mul_nonneg p.2.1 (growthWindow p x y).2.1)]
    congr 1
    simp only [growthStep, unitInterval.coe_symm_eq, Set.Icc.coe_mul]
    ring
  simp_rw [hpoint]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    growth_window_mass p x hx,
    ← ENNReal.ofReal_add (sub_nonneg.mpr p.2.2)
      (mul_nonneg (sub_nonneg.mpr p.2.2)
        (sub_nonneg.mpr (one_le_exp_iff.mpr (mul_nonneg p.2.1 hx.1)))),
    growth_coe p x hx]
  congr 1
  ring

theorem growth_continuation_mass (p : unitInterval) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    ∫⁻ y, (if x < y then 0 else ofReal (p : ℝ)) ∂unifUnit = ofReal ((p : ℝ) * x) := by
  have hfun : (fun y => if x < y then 0 else ofReal (p : ℝ)) =
      (Iic x).indicator (fun _ => ofReal (p : ℝ)) := by
    funext y
    by_cases h : x < y <;> simp [h, indicator_apply, not_le]
  rw [hfun]
  change (∫⁻ y, _ ∂volume.restrict (Icc (0 : ℝ) 1)) = _
  rw [ProbLang.TotalEris.Examples.lintegral_indicator_restrict measurableSet_Iic,
    upper_window x hx.2, setLIntegral_const, Real.volume_Icc, sub_zero,
    ← ENNReal.ofReal_mul p.2.1]

/-- A fixed threshold cap strictly below one supplies termination amplification. -/
def factor (B : unitInterval) : ℝ≥0 := ⟨1 / (B : ℝ), div_nonneg zero_le_one B.2.1⟩

theorem one_lt_factor (B : unitInterval) (hB : 0 < (B : ℝ) ∧ (B : ℝ) < 1) :
    1 < factor B := by
  change (1 : ℝ) < 1 / (B : ℝ)
  exact (one_lt_div hB.1).mpr hB.2

theorem amplified_continuation (p B : unitInterval) (hB : 0 < (B : ℝ)) (x : ℝ)
    (hx : 0 ≤ x ∧ x ≤ (B : ℝ)) (ε : ℝ≥0∞) :
    ofReal ((p : ℝ) * x) * (factor B * ε) ≤ ε := by
  have hpx : 0 ≤ (p : ℝ) * x := mul_nonneg p.2.1 hx.1
  have hamp : ofReal ((p : ℝ) * x) * factor B ≤ 1 := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hpx]
    apply ENNReal.ofReal_le_one.mpr
    change (p : ℝ) * x * (1 / (B : ℝ)) ≤ 1
    rw [mul_one_div, div_le_one hB]
    exact (mul_le_of_le_one_left hx.1 p.2.2).trans hx.2
  simpa only [mul_assoc] using (mul_le_of_le_one_left' hamp (a := ε))

end

end SampLib.ExponentialFactory
