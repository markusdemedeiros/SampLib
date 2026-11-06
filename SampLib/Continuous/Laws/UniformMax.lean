module

public import Metrology.ProbLang.Reals
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-! # The maximum of two independent unit uniforms

Tonelli splits the law into two successive uniform draws, and the CDF identifies the
Beta law.
-/

open Set ProbLang
open LawfulProbLangℝ (unifUnit)
open scoped ENNReal

namespace SampLib.UniformMax

noncomputable section

section mathematics

open MeasureTheory

/-- The second order statistic of two independent unit uniforms. -/
def law : Measure ℝ := (unifUnit.prod unifUnit).map (fun z : ℝ × ℝ => max z.1 z.2)

instance : IsProbabilityMeasure law := by unfold law; infer_instance

/-- Conditional credit after the first draw. -/
def credit (F : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ := ∫⁻ y, F (max x y) ∂unifUnit

theorem measurable_credit (F : ℝ → ℝ≥0∞) (hF : Measurable F) : Measurable (credit F) :=
  (hF.comp (measurable_fst.max measurable_snd)).lintegral_prod_right'

/-- Tonelli transports the maximum law to the two successive uniform draws. -/
theorem expectation_preservation (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, credit F x ∂unifUnit = ∫⁻ z, F z ∂law := by
  rw [law, lintegral_map hF (measurable_fst.max measurable_snd)]
  exact (lintegral_prod _ (hF.comp (measurable_fst.max measurable_snd)).aemeasurable).symm

/-- The CDF `P[max(U,V) ≤ t] = t²` identifies Beta(2,1). -/
theorem cdf (t : unitInterval) : law (Iic (t : ℝ)) = ENNReal.ofReal (t : ℝ) ^ 2 := by
  have hu : unifUnit (Iic (t : ℝ)) = ENNReal.ofReal (t : ℝ) := by
    change volume.restrict (Icc (0 : ℝ) 1) (Iic (t : ℝ)) = _
    rw [Measure.restrict_apply measurableSet_Iic, ← Ici_inter_Iic,
      inter_left_comm, Iic_inter_Iic, min_eq_left t.2.2, Ici_inter_Iic, Real.volume_Icc]
    simp
  have hset : (fun z : ℝ × ℝ => max z.1 z.2) ⁻¹' Iic (t : ℝ) =
      Iic (t : ℝ) ×ˢ Iic (t : ℝ) := by
    ext z
    change max z.1 z.2 ≤ (t : ℝ) ↔ z.1 ≤ (t : ℝ) ∧ z.2 ≤ (t : ℝ)
    exact max_le_iff
  rw [law, Measure.map_apply (measurable_fst.max measurable_snd) measurableSet_Iic,
    hset, Measure.prod_prod, hu, pow_two]

end mathematics

end

end SampLib.UniformMax
