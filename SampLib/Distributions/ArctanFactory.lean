module

public import SampLib.Distributions.DyadicPosterior
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-! # Averaging a reciprocal coin gives the arctangent factory

Conditioned on the shared uniform U, the inner reciprocal coin has success
probability `1/(1+(pU)^2)`. Averaging over U yields the continuous atan(p)/p law.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SampLib.ArctanFactory

noncomputable section

/-- Continuous extension at the deterministic zero-input coin. -/
def ratio (p : unitInterval) : unitInterval :=
  if hp : (p : ℝ) = 0 then 1 else
    ⟨Real.arctan p / p, div_nonneg (Real.arctan_nonneg.mpr p.2.1) p.2.1,
      (div_le_one (lt_of_le_of_ne p.2.1 (Ne.symm hp))).mpr (Real.arctan_le_self p.2.1)⟩

@[simp] theorem ratio_coe_zero : (ratio 0 : ℝ) = 1 := by simp [ratio]

theorem ratio_coe_of_ne_zero (p : unitInterval) (hp : (p : ℝ) ≠ 0) :
    (ratio p : ℝ) = Real.arctan p / p := by simp [ratio, hp]

/-- A linear change of variables evaluates the latent reciprocal integral. -/
theorem integral (p : unitInterval) :
    ∫ u in (0 : ℝ)..1, 1 / (1 + ((p : ℝ) * u) ^ 2) = (ratio p : ℝ) := by
  by_cases hp : (p : ℝ) = 0
  · simp [hp, ratio]
  · rw [intervalIntegral.integral_comp_mul_left
      (fun x : ℝ => 1 / (1 + x ^ 2)) hp]
    simp only [mul_zero, mul_one, smul_eq_mul]
    rw [integral_one_div_one_add_sq, Real.arctan_zero, sub_zero, ratio_coe_of_ne_zero p hp]
    ring

/-- This success-mass identity suffices for arbitrary, possibly infinite, continuation credits. -/
theorem success_mass (p : unitInterval) :
    (∫⁻ u, ENNReal.ofReal (1 / (1 + ((p : ℝ) * u) ^ 2)) ∂DyadicPosterior.unitLaw) =
      ENNReal.ofReal (ratio p : ℝ) := by
  have hc : Continuous (fun u : ℝ => 1 / (1 + ((p : ℝ) * u) ^ 2)) :=
    continuous_const.div (continuous_const.add ((continuous_const.mul continuous_id).pow 2))
      (fun u => by positivity)
  have hi : IntegrableOn (fun u : ℝ => 1 / (1 + ((p : ℝ) * u) ^ 2))
      (Ioc 0 1) volume := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    (hc.intervalIntegrable 0 1)
  have hn : ∀ᵐ u ∂volume.restrict (Ioc (0 : ℝ) 1),
      0 ≤ 1 / (1 + ((p : ℝ) * u) ^ 2) := Filter.Eventually.of_forall (fun u => by positivity)
  rw [DyadicPosterior.unitLaw]
  rw [restrict_Ico_eq_restrict_Ioc, ← ofReal_integral_eq_lintegral_ofReal hi hn]
  congr 1
  rw [← intervalIntegral.integral_of_le zero_le_one]
  exact integral p

end

end SampLib.ArctanFactory
