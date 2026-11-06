module

public import SampLib.Distributions.MaximumUniform
public import SampLib.Distributions.AcceptedProposal

@[expose] public section

/-! # Integer-shape incomplete-gamma integrals

The factor `n+1` in the maximum proposal cancels upon conditioning on acceptance.
-/

open Set MeasureTheory Real ProbLang
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.IntegerGammaKernel

noncomputable section

abbrev acceptance := ExponentialFactory.decay (1 : unitInterval)

/-- The lower incomplete gamma function at the positive integer shape `n+1`. -/
def lowerGamma (n : ℕ) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, t ^ n * exp (-t)

theorem weighted_integral (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ∫⁻ t in Icc (0 : ℝ) x,
      MaximumUniform.density n t * AcceptedProposal.weight acceptance t =
        ofReal (((n + 1 : ℕ) : ℝ) * lowerGamma n x) := by
  have hpoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) x) :
      MaximumUniform.density n t * AcceptedProposal.weight acceptance t =
        ofReal (((n + 1 : ℕ) : ℝ) * (t ^ n * exp (-t))) := by
    simp only [MaximumUniform.density, AcceptedProposal.weight, acceptance,
      ExponentialFactory.decay_coe _ _ ht.1, Set.Icc.coe_one, one_mul, neg_mul]
    rw [← ENNReal.ofReal_mul (mul_nonneg (by positivity) (pow_nonneg ht.1 _)), mul_assoc]
  rw [setLIntegral_congr_fun measurableSet_Icc hpoint,
    ProbLang.TotalEris.Examples.lintegral_ofReal_Icc hx (by fun_prop)
      (fun t ht => mul_nonneg (by positivity)
        (mul_nonneg (pow_nonneg ht.1 _) (exp_pos _).le)),
    intervalIntegral.integral_const_mul]
  rfl

theorem mass_eq (n : ℕ) : AcceptedProposal.mass (MaximumUniform.law n) acceptance =
    ofReal (((n + 1 : ℕ) : ℝ) * lowerGamma n 1) := by
  rw [AcceptedProposal.mass, MaximumUniform.law,
    lintegral_withDensity_eq_lintegral_mul _ (MaximumUniform.measurable_density n)
      (AcceptedProposal.measurable_weight _ (ExponentialFactory.measurable_decay 1))]
  exact weighted_integral n 1 zero_le_one

theorem window_mass (n : ℕ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    ∫⁻ t in Iio x, AcceptedProposal.weight acceptance t ∂MaximumUniform.law n =
      ofReal (((n + 1 : ℕ) : ℝ) * lowerGamma n x) := by
  rw [MaximumUniform.law, restrict_withDensity measurableSet_Iio,
    lintegral_withDensity_eq_lintegral_mul _ (MaximumUniform.measurable_density n)
      (AcceptedProposal.measurable_weight _ (ExponentialFactory.measurable_decay 1))]
  change (∫⁻ t, _ ∂(volume.restrict (Icc (0 : ℝ) 1)).restrict (Iio x)) = _
  have hs : Iio x ∩ Icc (0 : ℝ) 1 = Ico 0 x := by
    ext t
    simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.le.trans hx.2⟩⟩
  rw [Measure.restrict_restrict measurableSet_Iio, hs, restrict_Ico_eq_restrict_Icc]
  exact weighted_integral n x hx.1

end

end SampLib.IntegerGammaKernel
