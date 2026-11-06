import SampLib.Templates
import Samplers.Continuous
import Metrology.Iris.LocalBI

/-! # The maximum of two independent unit uniforms -/

open Set ProbLang
open ProbLangℝ (realLt)
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

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

/-- CTE specification for the maximum order statistic. -/
theorem twp_uniformMax (E : CoPset) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ⊢ ↯ (∫⁻ z, F z ∂law) -∗ tglWp E pl(&Occil.uniformMax #())
      (fun v : Val ℝ => iprop(∃ z : ℝ, ⌜v = Val.real z⌝ ∗ ↯ (F z))) := by
  iintro Hcredit
  twp_pures
  twp_bind pl(urand)
  iapply (twp_urand_exp (measurable_credit F hF) ?_) $$ Hcredit
  · rw [expectation_preservation F hF]
  iintro %x ⟨_, Hcredit⟩
  twp_pures
  twp_bind pl(urand)
  isimp only [credit] at Hcredit
  iapply (twp_urand_exp (ε₂ := fun y => F (max x y))
    (hF.comp (measurable_const.max measurable_id)) le_rfl) $$ Hcredit
  iintro %y ⟨_, Hcredit⟩
  twp_pures
  by_cases hxy : x < y
  · rw [show realLt x y = true from decide_eq_true hxy]
    twp_pures
    twp_value
    imodintro
    iexists (max x y)
    iframe Hcredit
    ipureintro
    exact Val.ext (by simp [max_eq_right hxy.le])
  · rw [show realLt x y = false from decide_eq_false hxy]
    twp_pures
    twp_value
    imodintro
    iexists (max x y)
    iframe Hcredit
    ipureintro
    exact Val.ext (by simp [max_eq_left (le_of_not_gt hxy)])

/-- Typed maximum-order-statistic specification. -/
theorem uniformMax_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.uniformMax #()) law Val.real where
  spec F hF := wand_entails (twp_uniformMax E F hF)

end specification

end

end SampLib.UniformMax
