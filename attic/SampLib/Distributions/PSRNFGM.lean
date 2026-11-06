module

public import SampLib.Common.Laws.DyadicPosterior
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! # The joint density in the lazy FGM copula sampler -/

open Set MeasureTheory
open scoped ENNReal

namespace SampLib.PSRNFGM

noncomputable section

/-- The centered coordinate whose uniform expectation vanishes. -/
def centered (x : ℝ) : ℝ := 1 - 2 * x

/-- Density relative to two independent unit uniforms. -/
def densityReal (θ : ℝ) (z : ℝ × ℝ) : ℝ :=
  1 + θ * centered z.1 * centered z.2

private theorem integrable_centered : Integrable centered DyadicPosterior.unitLaw := by
  exact ((continuous_const.sub (continuous_const.mul continuous_id)).integrableOn_Icc
    : IntegrableOn centered (Icc 0 1)).mono_set Ico_subset_Icc_self

/-- Each coordinate contributes no average interaction. -/
theorem integral_centered : ∫ x, centered x ∂DyadicPosterior.unitLaw = 0 := by
  change (∫ x in Ico (0 : ℝ) 1, 1 - 2 * x) = 0
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  rw [intervalIntegral.integral_sub (intervalIntegrable_const)
      ((show Continuous (fun x : ℝ => 2 * x) by fun_prop).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, integral_id]
  norm_num

/-- On the unit square the interaction cannot change the density by more than one. -/
theorem density_bounds {θ : ℝ} (hθ : θ ∈ Icc (-1) 1) {z : ℝ × ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    densityReal θ z ∈ Icc 0 2 := by
  have hx : |centered z.1| ≤ 1 := by
    rw [abs_le]
    constructor <;> dsimp [centered] <;> linarith [hz.1.1, hz.1.2]
  have hy : |centered z.2| ≤ 1 := by
    rw [abs_le]
    constructor <;> dsimp [centered] <;> linarith [hz.2.1, hz.2.2]
  have ht : |θ| ≤ 1 := abs_le.mpr hθ
  have hb : |θ * centered z.1 * centered z.2| ≤ 1 := by
    have htx : |θ * centered z.1| ≤ 1 := by
      simpa only [abs_mul, mul_one] using mul_le_mul ht hx (abs_nonneg _) zero_le_one
    simpa only [abs_mul, mul_one] using mul_le_mul htx hy (abs_nonneg _) zero_le_one
  rcases abs_le.mp hb with ⟨hl, hu⟩
  constructor <;> dsimp [densityReal] <;> linarith

/-- The independent proposal before conditioning on acceptance. -/
def proposal : Measure (ℝ × ℝ) :=
  DyadicPosterior.unitLaw.prod DyadicPosterior.unitLaw

instance : IsProbabilityMeasure proposal := by unfold proposal; infer_instance

private theorem integrable_densityReal (θ : ℝ) : Integrable (densityReal θ) proposal := by
  unfold densityReal proposal
  simpa only [Pi.add_def, mul_assoc] using
    (integrable_const (1 : ℝ)).add
      ((integrable_centered.mul_prod integrable_centered).const_mul θ)

/-- Independence and the zero centered mean normalize the joint density. -/
theorem integral_densityReal (θ : ℝ) : ∫ z, densityReal θ z ∂proposal = 1 := by
  simp only [densityReal, mul_assoc, proposal]
  rw [integral_add (integrable_const (1 : ℝ))
      ((integrable_centered.mul_prod integrable_centered).const_mul θ),
    integral_const_mul, integral_prod_mul, integral_centered]
  simp

private theorem ae_mem_square :
    ∀ᵐ z ∂proposal, z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  have hu : ∀ᵐ x ∂DyadicPosterior.unitLaw, x ∈ Ico (0 : ℝ) 1 := by
    simpa only [DyadicPosterior.law_nil] using DyadicPosterior.ae_mem_unit []
  apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Icc.prod measurableSet_Icc)).mpr
  filter_upwards [hu] with x hx
  exact hu.mono fun y hy => ⟨⟨hx.1, hx.2.le⟩, ⟨hy.1, hy.2.le⟩⟩

/-- The intended dependent FGM law, without discarding the accepted pair's correlation. -/
def law (θ : ℝ) : Measure (ℝ × ℝ) :=
  proposal.withDensity (fun z => ENNReal.ofReal (densityReal θ z))

theorem isProbabilityMeasure_law {θ : ℝ} (hθ : θ ∈ Icc (-1) 1) :
    IsProbabilityMeasure (law θ) := by
  have hn : 0 ≤ᵐ[proposal] densityReal θ :=
    ae_mem_square.mono fun _ hz => (density_bounds hθ hz).1
  refine ⟨?_⟩
  rw [law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_densityReal θ) hn,
    integral_densityReal]
  simp

/-- The accepted pair's joint credit is weighted by the full copula density. -/
theorem expectation_preservation (θ : ℝ) (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F z ∂law θ =
      ∫⁻ z, ENNReal.ofReal (densityReal θ z) * F z ∂proposal := by
  rw [law, lintegral_withDensity_eq_lintegral_mul _ (by unfold densityReal centered; fun_prop) hF]
  simp only [Pi.mul_apply]

end

end SampLib.PSRNFGM
