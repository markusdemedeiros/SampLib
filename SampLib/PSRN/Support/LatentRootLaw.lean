import SampLib.PSRN.Support.LatentRootModel
import SampLib.PSRN.Support.LatentRealMap
import SampLib.PSRN.Laws.PSRNRayleigh

/-! # Observable laws of the shared deferred-root model -/

open MeasureTheory ProbabilityTheory

namespace SampLib.LatentReal.Model

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω]

/-- Rooting changes the real projection while retaining the whole source law. -/
theorem nthRoot_law (D : Model Ω S) (degree : ℕ) (s : S) :
    (D.nthRoot degree).law s = (D.law s).map (root degree) := by
  have hm : Measurable (root degree) := by unfold root; exact measurable_id.pow_const _
  rw [law, law, Measure.map_map hm D.measurable_value]
  rfl

/-- The actual Rayleigh transformation is the square root of twice one exponential draw. -/
theorem rayleigh_law (D : Model Ω S) (s : S) (hD : D.law s = expMeasure 1) :
    ((D.scale 2).nthRoot 2).law s = PSRNRayleigh.law := by
  have hm : Measurable (root 2) := by unfold root; exact measurable_id.pow_const _
  rw [nthRoot_law, scale_law, hD, Measure.map_map hm (by fun_prop)]
  congr 1
  funext x
  simp [root, PSRNRayleigh.transform, Real.sqrt_eq_rpow, mul_comm]

private theorem exponential_nonneg : ∀ᵐ x ∂expMeasure 1, 0 ≤ x := by
  have hzero : expMeasure 1 (Set.Iio 0) = 0 := by
    change (volume.withDensity (exponentialPDF 1)) (Set.Iio 0) = 0
    rw [withDensity_apply _ measurableSet_Iio]
    exact lintegral_exponentialPDF_of_nonpos (le_refl 0)
  apply ae_iff.mpr
  convert hzero using 2
  ext x
  simp

/-- A continuous exponential source meets every threshold obligation of the Rayleigh root. -/
theorem rayleigh_admissible (D : Model Ω S) (s : S) (hD : D.law s = expMeasure 1) :
    Root.Admissible (D.scale 2) 2 s := by
  let _ : NullSingletonClass (D.law s) := by
    rw [hD]
    change NullSingletonClass (volume.withDensity (exponentialPDF 1))
    infer_instance
  have hnonneg : ∀ᵐ x ∂D.posterior s, 0 ≤ D.value x := by
    have h := exponential_nonneg
    rw [← hD] at h
    exact ae_of_ae_map D.measurable_value.aemeasurable h
  refine ⟨hnonneg.mono (fun x hx => mul_nonneg hx (by norm_num)), ?_⟩
  intro a b _ _
  have hne : ∀ᵐ x ∂D.posterior s, D.value x ≠ (((a : ℝ) / b) ^ 2) / 2 :=
    ae_of_ae_map D.measurable_value.aemeasurable
      ((D.law s).ae_ne ((((a : ℝ) / b) ^ 2) / 2))
  exact hne.mono fun x hx heq => hx ((eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).mpr heq)

end

end SampLib.LatentReal.Model
