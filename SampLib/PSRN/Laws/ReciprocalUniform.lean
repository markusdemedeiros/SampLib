module

public import Mathlib.Probability.Distributions.Pareto
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

@[expose] public section

/-! # The inverse of a unit uniform is Pareto(1,1)

The inverse threshold has unit-interval length `1-1/t`. Integrating the Pareto
tail density gives the same distribution function, including both endpoints.
-/

open Set MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace SampLib.ReciprocalUniform

noncomputable section

/-- The exact pushforward law of the reciprocal-uniform sampler. -/
def law : Measure ℝ := (volume.restrict (Ico (0 : ℝ) 1)).map (fun x => 1 / x)

instance : IsProbabilityMeasure law := by
  have : IsProbabilityMeasure (volume.restrict (Ico (0 : ℝ) 1)) :=
    ⟨by norm_num [Measure.restrict_apply]⟩
  unfold law
  infer_instance

/-- A measurable continuation may be unbounded or infinite. -/
theorem expectation (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x ∂law) = ∫⁻ u in Ico (0 : ℝ) 1, F (1 / u) :=
  lintegral_map hF (measurable_const.div measurable_id)

/-- Reciprocal thresholds cut a single interval out of the unit uniform. -/
theorem law_Iic (t : ℝ) : law (Iic t) = ENNReal.ofReal (if 1 ≤ t then 1 - 1 / t else 0) := by
  have hm : Measurable (fun x : ℝ => 1 / x) := measurable_const.div measurable_id
  rw [law, Measure.map_apply hm measurableSet_Iic, restrict_Ico_eq_restrict_Ioc,
    Measure.restrict_apply (measurableSet_Iic.preimage hm)]
  by_cases ht : 1 ≤ t
  · rw [ite_eq_left ht]
    have ht0 : 0 < t := zero_lt_one.trans_le ht
    have heq : ((fun x : ℝ => 1 / x) ⁻¹' Iic t) ∩ Ioc 0 1 = Icc (1 / t) 1 := by
      ext x
      change (1 / x ≤ t ∧ 0 < x ∧ x ≤ 1) ↔ 1 / t ≤ x ∧ x ≤ 1
      constructor
      · rintro ⟨hinv, hx, hx1⟩
        exact ⟨(one_div_le hx ht0).mp hinv, hx1⟩
      · rintro ⟨hx, hx1⟩
        have hx0 : 0 < x := (div_pos zero_lt_one ht0).trans_le hx
        exact ⟨(one_div_le hx0 ht0).mpr hx, hx0, hx1⟩
    rw [heq, Real.volume_Icc]
  · rw [ite_eq_right ht]
    have heq : ((fun x : ℝ => 1 / x) ⁻¹' Iic t) ∩ Ioc 0 1 = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hx0, hx1⟩
      exact ht ((one_le_one_div hx0 hx1).trans hx)
    rw [heq, measure_empty, ENNReal.ofReal_zero]

private theorem pareto_tail (t : ℝ) (ht : 1 ≤ t) :
    paretoMeasure 1 1 (Ioi t) = ENNReal.ofReal (1 / t) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hpdf (y : ℝ) (hy : y ∈ Ioi t) : paretoPDF 1 1 y = ENNReal.ofReal (y ^ (-2 : ℝ)) := by
    rw [paretoPDF_of_le (ht.trans hy.le)]
    norm_num
  calc
    _ = ∫⁻ y in Ioi t, ENNReal.ofReal (y ^ (-2 : ℝ)) := by
      rw [paretoMeasure, withDensity_apply _ measurableSet_Ioi]
      exact setLIntegral_congr_fun measurableSet_Ioi hpdf
    _ = ENNReal.ofReal (∫ y in Ioi t, y ^ (-2 : ℝ)) := by
      symm
      apply ofReal_integral_eq_lintegral_ofReal
        (integrableOn_Ioi_rpow_of_lt (by norm_num) ht0)
      exact (ae_restrict_iff' measurableSet_Ioi).mpr
        (ae_of_all _ fun y hy => (rpow_pos_of_pos (ht0.trans hy) _).le)
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ht0]
      norm_num [one_div, Real.rpow_neg_one]

private theorem pareto_Iic (t : ℝ) :
    paretoMeasure 1 1 (Iic t) = ENNReal.ofReal (if 1 ≤ t then 1 - 1 / t else 0) := by
  have : IsProbabilityMeasure (paretoMeasure 1 1) :=
    isProbabilityMeasure_paretoMeasure (by norm_num) (by norm_num)
  by_cases ht : 1 ≤ t
  · rw [ite_eq_left ht]
    calc
      _ = paretoMeasure 1 1 (Ioi t)ᶜ := by rw [compl_Ioi]
      _ = 1 - paretoMeasure 1 1 (Ioi t) := by
        rw [measure_compl measurableSet_Ioi (measure_ne_top _ _), measure_univ]
      _ = _ := by
        rw [pareto_tail t ht, ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
  · rw [ite_eq_right ht, ENNReal.ofReal_zero, paretoMeasure,
      withDensity_apply _ measurableSet_Iic]
    calc
      _ = ∫⁻ _ in Iic t, (0 : ℝ≥0∞) :=
        setLIntegral_congr_fun measurableSet_Iic fun y hy =>
          paretoPDF_of_lt (hy.trans_lt (not_le.mp ht))
      _ = 0 := lintegral_zero

/-- Canonical scale-one, shape-one Pareto identification. -/
theorem law_eq_pareto : law = paretoMeasure 1 1 := by
  apply Measure.ext_of_Iic
  intro t
  rw [law_Iic, pareto_Iic]

end

end SampLib.ReciprocalUniform
