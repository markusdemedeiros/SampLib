module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import SampLib.Common.Laws.AcceptedProposal

@[expose] public section

/-! # The exponential-envelope identity for the hyperbolic-secant law -/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace SampLib.PSRNHyperbolicSecant

noncomputable section

/-- The acceptance probability applied to the same exponential proposal. -/
def acceptance (x : ℝ) : unitInterval :=
  ⟨1 / (1 + Real.exp (-2 * x)), by
    constructor
    · positivity
    · exact (div_le_one (by positivity)).mpr (by linarith [Real.exp_pos (-2 * x)])⟩

@[fun_prop] theorem measurable_acceptance : Measurable acceptance := by
  apply Measurable.subtype_mk
  fun_prop

theorem acceptance_pos (x : ℝ) : 0 < (acceptance x : ℝ) := by
  dsimp [acceptance]
  positivity

/-- The unnormalized density of an accepted positive proposal. -/
def envelope (x : ℝ) : ℝ := Real.exp (-x) / (1 + Real.exp (-2 * x))

/-- The exponential envelope is half a hyperbolic secant. -/
theorem envelope_eq (x : ℝ) : envelope x = 1 / (2 * Real.cosh x) := by
  rw [envelope, show -2 * x = -x + -x by ring, Real.exp_add, Real.cosh_eq,
    Real.exp_neg]
  field_simp

private theorem primitive_deriv (x : ℝ) :
    HasDerivAt (fun x => -Real.arctan (Real.exp (-x))) (envelope x) x := by
  have h := (((hasDerivAt_id x).neg.exp).arctan).neg
  convert h using 1
  · rfl
  · dsimp [envelope]
    rw [show -2 * x = -x + -x by ring, Real.exp_add]
    ring

private theorem primitive_limit :
    Tendsto (fun x => -Real.arctan (Real.exp (-x))) atTop (𝓝 0) := by
  simpa using (Real.continuous_arctan.tendsto 0).comp
    Real.tendsto_exp_neg_atTop_nhds_zero |>.neg

/-- The exponential envelope has acceptance mass π/4; `-arctan(exp(-x))` is its primitive. -/
theorem integral_envelope : ∫ x in Ioi (0 : ℝ), envelope x = Real.pi / 4 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := (0 : ℝ)) (fun x _ => primitive_deriv x)
    (fun x _ => by dsimp [envelope]; positivity) primitive_limit
  simpa [Real.arctan_one] using h

private theorem integrable_envelope : IntegrableOn envelope (Ioi (0 : ℝ)) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun x _ => primitive_deriv x)
    (fun x _ => by dsimp [envelope]; positivity) primitive_limit

private theorem weighted_exponentialPDF (x : ℝ) :
    exponentialPDF 1 x * AcceptedProposal.weight acceptance x =
      (Ici (0 : ℝ)).indicator (fun x => ENNReal.ofReal (envelope x)) x := by
  by_cases hx : 0 ≤ x
  · rw [exponentialPDF_of_nonneg hx,
      indicator_of_mem (show x ∈ Ici (0 : ℝ) from hx)]
    simp only [one_mul, AcceptedProposal.weight, acceptance, Subtype.coe_mk]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    simp [envelope, div_eq_mul_inv]
  · rw [indicator_of_notMem (show x ∉ Ici (0 : ℝ) from hx),
      exponentialPDF_of_neg (lt_of_not_ge hx), zero_mul]

/-- The normalizing constant is the acceptance probability of the exponential proposal. -/
theorem acceptance_mass :
    AcceptedProposal.mass (expMeasure 1) acceptance = ENNReal.ofReal (Real.pi / 4) := by
  change (∫⁻ x, AcceptedProposal.weight acceptance x
    ∂volume.withDensity (exponentialPDF 1)) = _
  have hpdf : Measurable (exponentialPDF 1) :=
    ENNReal.measurable_ofReal.comp (measurable_exponentialPDFReal 1)
  rw [lintegral_withDensity_eq_lintegral_mul _ hpdf
    (AcceptedProposal.measurable_weight acceptance measurable_acceptance)]
  simp only [Pi.mul_apply]
  simp_rw [weighted_exponentialPDF]
  rw [lintegral_indicator measurableSet_Ici, ← restrict_Ioi_eq_restrict_Ici,
    ← ofReal_integral_eq_lintegral_ofReal integrable_envelope
      (ae_of_all _ (fun x => by dsimp [envelope]; positivity)), integral_envelope]

private instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

theorem acceptance_mass_ne_zero : AcceptedProposal.mass (expMeasure 1) acceptance ≠ 0 := by
  rw [acceptance_mass]
  exact (ENNReal.ofReal_pos.mpr (by positivity : 0 < Real.pi / 4)).ne'

/-- Law of the accepted positive proposal. -/
def positiveLaw : Measure ℝ :=
  AcceptedProposal.law (expMeasure 1) acceptance acceptance_mass_ne_zero

instance : IsProbabilityMeasure positiveLaw := by unfold positiveLaw; infer_instance

/-- The normalized positive-half density in exponential-envelope form. -/
def positiveDensity (x : ℝ) : ℝ :=
  if 0 ≤ x then 4 / Real.pi * envelope x else 0

@[fun_prop] theorem measurable_positiveDensity : Measurable positiveDensity := by
  unfold positiveDensity envelope
  exact Measurable.ite (p := fun x : ℝ => 0 ≤ x) measurableSet_Ici
    (by fun_prop) measurable_const

/-- The accepted law has its explicit normalized positive-half density. -/
theorem positiveLaw_eq_withDensity :
    positiveLaw = volume.withDensity (fun x => ENNReal.ofReal (positiveDensity x)) := by
  have hpdf : Measurable (exponentialPDF 1) :=
    ENNReal.measurable_ofReal.comp (measurable_exponentialPDFReal 1)
  have hweight := AcceptedProposal.measurable_weight acceptance measurable_acceptance
  rw [positiveLaw, AcceptedProposal.law, acceptance_mass]
  change (ENNReal.ofReal (Real.pi / 4))⁻¹ •
    (volume.withDensity (exponentialPDF 1)).withDensity
      (AcceptedProposal.weight acceptance) = _
  rw [← withDensity_mul volume hpdf hweight, ← withDensity_smul _ (hpdf.mul hweight)]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, weighted_exponentialPDF]
  rw [← ENNReal.ofReal_inv_of_pos (by positivity : 0 < Real.pi / 4)]
  by_cases hx : 0 ≤ x
  · rw [indicator_of_mem (show x ∈ Ici (0 : ℝ) from hx)]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (Real.pi / 4)⁻¹)]
    simp [positiveDensity, hx, div_eq_mul_inv, mul_inv_rev]
  · rw [indicator_of_notMem (show x ∉ Ici (0 : ℝ) from hx), mul_zero]
    simp [positiveDensity, hx]

private theorem neg_positiveLaw_eq_withDensity :
    positiveLaw.map (fun x => -x) =
      volume.withDensity (fun x => ENNReal.ofReal (positiveDensity (-x))) := by
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  have hp : Measurable (fun x => ENNReal.ofReal (positiveDensity x)) :=
    ENNReal.measurable_ofReal.comp measurable_positiveDensity
  have hn : Measurable (fun x => ENNReal.ofReal (positiveDensity (-x))) :=
    hp.comp measurable_neg
  have hFn : Measurable (fun x => F (-x)) := hF.comp measurable_neg
  rw [lintegral_map hF measurable_neg, positiveLaw_eq_withDensity,
    lintegral_withDensity_eq_lintegral_mul _ hp hFn,
    lintegral_withDensity_eq_lintegral_mul _ hn hF]
  have hm : Measurable (fun x => ENNReal.ofReal (positiveDensity (-x)) * F x) := hn.mul hF
  simpa only [Pi.mul_apply, neg_neg] using (Measure.measurePreserving_neg volume).lintegral_comp hm

/-- Symmetrizing the accepted exponential gives the natural-scale hyperbolic-secant law. -/
def law : Measure ℝ :=
  (ENNReal.ofReal (1 / 2 : ℝ) • positiveLaw) +
    (ENNReal.ofReal (1 / 2 : ℝ) • positiveLaw.map (fun x => -x))

instance : IsProbabilityMeasure law where
  measure_univ := by simpa [law] using ENNReal.inv_two_add_inv_two

/-- The symmetrized law has the standard density `sech(x)/π`. -/
theorem law_eq_withDensity :
    law = volume.withDensity (fun x => ENNReal.ofReal (1 / (Real.pi * Real.cosh x))) := by
  have hp : Measurable (fun x => ENNReal.ofReal (positiveDensity x)) :=
    ENNReal.measurable_ofReal.comp measurable_positiveDensity
  have hn : Measurable (fun x => ENNReal.ofReal (positiveDensity (-x))) :=
    hp.comp measurable_neg
  rw [law, neg_positiveLaw_eq_withDensity, positiveLaw_eq_withDensity,
    ← withDensity_smul _ hp, ← withDensity_smul _ hn, ← withDensity_add_left (hp.const_smul _)]
  apply withDensity_congr_ae
  filter_upwards [(volume : Measure ℝ).ae_ne (0 : ℝ)] with x hx
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hpos : 0 < x
  · simp only [positiveDensity, ite_eq_left hpos.le, ite_eq_right (by linarith : ¬0 ≤ -x),
      ENNReal.ofReal_zero, mul_zero, add_zero]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), envelope_eq]
    congr 1
    field_simp
    norm_num
  · have hneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hx
    simp only [positiveDensity, ite_eq_right hneg.not_ge, ite_eq_left (neg_pos.mpr hneg).le,
      ENNReal.ofReal_zero, mul_zero, zero_add]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), envelope_eq, Real.cosh_neg]
    congr 1
    field_simp
    norm_num

/-- Both signs share the accepted proposal; arbitrary continuation credits may be infinite. -/
theorem expectation_preservation (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂law =
      ENNReal.ofReal (1 / 2 : ℝ) *
        ((∫⁻ x, F x ∂positiveLaw) + ∫⁻ x, F (-x) ∂positiveLaw) := by
  simp only [law, lintegral_add_measure, lintegral_smul_measure, smul_eq_mul,
    lintegral_map hF measurable_neg]
  ring

end

end SampLib.PSRNHyperbolicSecant
