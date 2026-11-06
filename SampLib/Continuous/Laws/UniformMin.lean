module

public import Metrology.ProbLang.Reals
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-! # The minimum of two independent unit uniforms

Tonelli splits the law into two successive uniform draws, and the CDF identifies the
Beta law.
-/

open Set ProbLang
open LawfulProbLangℝ (unifUnit)
open scoped ENNReal

namespace SampLib.UniformMin

noncomputable section

section mathematics

open MeasureTheory

/-- The first order statistic of two independent unit uniforms. -/
def law : Measure ℝ := (unifUnit.prod unifUnit).map (fun z : ℝ × ℝ => min z.1 z.2)

instance : IsProbabilityMeasure law := by unfold law; infer_instance

/-- Conditional credit after the first draw. -/
def credit (F : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ := ∫⁻ y, F (min x y) ∂unifUnit

theorem measurable_credit (F : ℝ → ℝ≥0∞) (hF : Measurable F) : Measurable (credit F) :=
  (hF.comp (measurable_fst.min measurable_snd)).lintegral_prod_right'

/-- Tonelli transports the minimum law to the two successive uniform draws. -/
theorem expectation_preservation (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, credit F x ∂unifUnit = ∫⁻ z, F z ∂law := by
  rw [law, lintegral_map hF (measurable_fst.min measurable_snd)]
  exact (lintegral_prod _ (hF.comp (measurable_fst.min measurable_snd)).aemeasurable).symm

/-- The survival function `P[min(U,V) > t] = (1-t)²` identifies Beta(1,2). -/
theorem survival (t : unitInterval) : law (Ioi (t : ℝ)) = ENNReal.ofReal (1 - (t : ℝ)) ^ 2 := by
  have hu : unifUnit (Iic (t : ℝ)) = ENNReal.ofReal (t : ℝ) := by
    change volume.restrict (Icc (0 : ℝ) 1) (Iic (t : ℝ)) = _
    rw [Measure.restrict_apply measurableSet_Iic, ← Ici_inter_Iic,
      inter_left_comm, Iic_inter_Iic, min_eq_left t.2.2, Ici_inter_Iic, Real.volume_Icc]
    simp
  have ht : unifUnit (Ioi (t : ℝ)) = ENNReal.ofReal (1 - (t : ℝ)) := by
    rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, hu,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ t.2.1]
  have hset : (fun z : ℝ × ℝ => min z.1 z.2) ⁻¹' Ioi (t : ℝ) =
      Ioi (t : ℝ) ×ˢ Ioi (t : ℝ) := by ext z; simp [lt_min_iff]
  rw [law, Measure.map_apply (measurable_fst.min measurable_snd) measurableSet_Ioi,
    hset, Measure.prod_prod, ht, pow_two]

end mathematics

end

end SampLib.UniformMin
