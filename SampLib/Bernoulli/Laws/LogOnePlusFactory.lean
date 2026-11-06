module

public import SampLib.Common.Laws.DyadicPosterior
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.UnitInterval

@[expose] public section

/-! # The uniform reciprocal integral for log(1+p)

Keeping the factor p inside the integral gives a single fundamental-theorem
argument for the whole unit interval, including p=0.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SampLib.LogOnePlusFactory

noncomputable section

/-- The logarithmic factory's normalized target bias. -/
def bias (p : unitInterval) : unitInterval :=
  ⟨Real.log (1 + (p : ℝ)),
    Real.log_nonneg (by linarith [p.2.1]), by
      have h := Real.log_le_sub_one_of_pos (by linarith [p.2.1] : 0 < 1 + (p : ℝ))
      linarith [p.2.2]⟩

private theorem denominator_pos (p : unitInterval) (u : ℝ) (hu : u ∈ Icc 0 1) :
    0 < 1 + (p : ℝ) * u :=
  add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg p.2.1 hu.1)

private theorem continuousOn_integrand (p : unitInterval) :
    ContinuousOn (fun u : ℝ => (p : ℝ) / (1 + (p : ℝ) * u)) (Icc 0 1) :=
  continuous_const.continuousOn.div
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
    (fun u hu => (denominator_pos p u hu).ne')

/-- The derivative of log(1+pu) integrates directly, without dividing by p. -/
theorem integral (p : unitInterval) :
    ∫ u in (0 : ℝ)..1, (p : ℝ) / (1 + (p : ℝ) * u) = Real.log (1 + (p : ℝ)) := by
  have hd (u : ℝ) (hu : u ∈ uIcc 0 1) :
      HasDerivAt (fun u => Real.log (1 + (p : ℝ) * u))
        ((p : ℝ) / (1 + (p : ℝ) * u)) u := by
    have hu' : u ∈ Icc 0 1 := by simpa only [uIcc_of_le zero_le_one] using hu
    simpa only [Pi.add_apply, id_eq, zero_add, mul_one] using
      (((hasDerivAt_const u (1 : ℝ)).add ((hasDerivAt_id u).const_mul (p : ℝ))).log
        (denominator_pos p u hu').ne')
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (ContinuousOn.intervalIntegrable_of_Icc zero_le_one (continuousOn_integrand p))
  simpa only [mul_one, mul_zero, add_zero, Real.log_one, sub_zero] using h

/-- The exact success mass under the normalized initial uniform posterior. -/
theorem lintegral (p : unitInterval) :
    (∫⁻ u, ENNReal.ofReal ((p : ℝ) / (1 + (p : ℝ) * u)) ∂DyadicPosterior.unitLaw) =
      ENNReal.ofReal (bias p : ℝ) := by
  have hi : IntegrableOn (fun u : ℝ => (p : ℝ) / (1 + (p : ℝ) * u)) (Ioc 0 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (ContinuousOn.intervalIntegrable_of_Icc zero_le_one (continuousOn_integrand p))
  have hn : ∀ᵐ u ∂volume.restrict (Ioc (0 : ℝ) 1),
      0 ≤ (p : ℝ) / (1 + (p : ℝ) * u) :=
    (ae_restrict_mem measurableSet_Ioc).mono fun u hu =>
      div_nonneg p.2.1 (denominator_pos p u ⟨hu.1.le, hu.2⟩).le
  rw [DyadicPosterior.unitLaw, restrict_Ico_eq_restrict_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal hi hn]
  congr 1
  rw [← intervalIntegral.integral_of_le zero_le_one]
  exact integral p

end

end SampLib.LogOnePlusFactory
