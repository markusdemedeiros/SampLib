module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # Integrating a positive constant to a uniform real exponent -/

namespace SampLib.PowerIntegral

/-- The logarithmic mean is the average of the exponential interpolation. -/
theorem integral_const_power {p : ℝ} (hp : 0 < p) :
    (∫ u : ℝ in 0..1, p ^ u) = if p = 1 then 1 else (p - 1) / Real.log p := by
  by_cases h : p = 1
  · simp [h]
  · have hlog := Real.log_ne_zero_of_pos_of_ne_one hp h
    have hf : (fun u : ℝ => p ^ u) = (fun u => Real.exp (u * Real.log p)) := by
      funext u
      rw [Real.rpow_def_of_pos hp, mul_comm]
    rw [hf, intervalIntegral.integral_comp_mul_right Real.exp hlog, integral_exp]
    simp only [zero_mul, one_mul, Real.exp_zero, Real.exp_log hp, smul_eq_mul, ite_eq_right h]
    ring

end SampLib.PowerIntegral
