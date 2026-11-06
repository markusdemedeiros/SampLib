import SampLib.Templates
import Samplers.Continuous
import Metrology.Iris.LocalBI
import SampLib.Continuous.Laws.UniformMax

/-! # The maximum of two independent unit uniforms -/

open Set ProbLang
open ProbLangℝ (realLt)
open LawfulProbLangℝ (unifUnit)
open scoped ENNReal

namespace SampLib.UniformMax

noncomputable section

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
