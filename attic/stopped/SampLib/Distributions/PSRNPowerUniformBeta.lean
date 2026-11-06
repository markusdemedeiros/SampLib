import SampLib.PSRN.Laws.JohnkBeta
import SampLib.Common.Laws.DyadicPosterior

/-! # A positive power of a unit uniform has a beta law

For `c > 0`, substituting `u = t ^ c` on `(0, 1)` has Jacobian `c t ^ (c - 1)`, which is
exactly the `Beta(c, 1)` density. Hence `U ^ (1 / c)` has law `Beta(c, 1)`.
-/

open MeasureTheory ProbabilityTheory Set Real
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.PSRNPowerUniformBeta

noncomputable section

private theorem image_rpow {c : ℝ} (hc : 0 < c) :
    (fun t : ℝ => t ^ c) '' Ioo 0 1 = Ioo 0 1 := by
  ext u
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    exact ⟨rpow_pos_of_pos ht0 c, rpow_lt_one ht0.le ht1 hc⟩
  · rintro ⟨hu0, hu1⟩
    refine ⟨u ^ c⁻¹, ⟨rpow_pos_of_pos hu0 _, rpow_lt_one hu0.le hu1 (inv_pos.mpr hc)⟩, ?_⟩
    simp only [← rpow_mul hu0.le, inv_mul_cancel₀ hc.ne', rpow_one]

private theorem density {c t : ℝ} (hc : 0 < c) (ht : t ∈ Ioo (0 : ℝ) 1) :
    betaPDF c 1 t = ofReal |c * t ^ (c - 1)| := by
  rw [abs_of_pos (mul_pos hc (rpow_pos_of_pos ht.1 _))]
  simp [betaPDF, betaPDFReal, ht.1, ht.2, JohnkBeta.beta_one c hc]

/-- The unit uniform raised to `1 / c` has law `Beta(c, 1)`. -/
theorem map_rpow_inv (c : ℝ) (hc : 0 < c) :
    DyadicPosterior.unitLaw.map (fun u => u ^ c⁻¹) = betaMeasure c 1 := by
  have hm : Measurable fun u : ℝ => u ^ c⁻¹ := by fun_prop
  have hβ : Measurable (betaPDF c 1) :=
    ENNReal.measurable_ofReal.comp (measurable_betaPDFReal c 1)
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  have hsupport : Function.support (fun t => betaPDF c 1 t * F t) ⊆ Ioo 0 1 := by
    intro t ht
    by_contra hnot
    apply ht
    simp [betaPDF, betaPDFReal, show ¬(0 < t ∧ t < 1) from hnot]
  have hderiv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivWithinAt (fun t : ℝ => t ^ c) (c * t ^ (c - 1)) (Ioo 0 1) t :=
    (hasDerivAt_rpow_const (Or.inl ht.1.ne')).hasDerivWithinAt
  have hinj : InjOn (fun t : ℝ => t ^ c) (Ioo 0 1) := fun s hs t ht hst =>
    (strictMonoOn_rpow_Ici_of_exponent_pos hc).injOn hs.1.le ht.1.le hst
  calc
    _ = ∫⁻ u in Ioo 0 1, F (u ^ c⁻¹) := by
      rw [lintegral_map hF hm, DyadicPosterior.unitLaw,
        Measure.restrict_congr_set Ioo_ae_eq_Ico.symm]
    _ = ∫⁻ t in Ioo 0 1, ofReal |c * t ^ (c - 1)| * F ((t ^ c) ^ c⁻¹) := by
      conv_lhs => rw [← image_rpow hc]
      exact lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hderiv hinj _
    _ = ∫⁻ t in Ioo 0 1, betaPDF c 1 t * F t := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
      rw [density hc ht, ← rpow_mul ht.1.le, mul_inv_cancel₀ hc.ne', rpow_one]
    _ = ∫⁻ t, betaPDF c 1 t * F t := setLIntegral_eq_of_support_subset hsupport
    _ = _ := by
      rw [betaMeasure, lintegral_withDensity_eq_lintegral_mul _ hβ hF]
      rfl

end

end SampLib.PSRNPowerUniformBeta
