import SampLib.Templates
import Samplers.Continuous
import Metrology.Iris.LocalBI
import SampLib.Continuous.Laws.UniformSum

/-! # Irwin–Hall sampling by independent unit-uniform sums -/

open Set ProbLang
open LawfulProbLangℝ (unifUnit)
open scoped ENNReal

namespace SampLib.UniformSum

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

/-- CTE specification for every nonnegative number of uniforms. -/
theorem twp_uniformSum (E : CoPset) (n : ℕ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ⊢ ↯ (∫⁻ z, F z ∂law n) -∗ tglWp E pl(&Occil.uniformSum #int (n : ℤ))
      (fun v : Val ℝ => iprop(∃ z : ℝ, ⌜v = Val.real z⌝ ∗ ↯ (F z))) := by
  induction n generalizing F with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists (0 : ℝ)
    isimp only [law, MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    ipureintro
    exact Val.ext (by simp)
  | succ n ih =>
    iintro Hcredit
    twp_pures
    twp_bind pl(urand)
    iapply (twp_urand_exp (measurable_credit n F hF) ?_) $$ Hcredit
    · rw [expectation_preservation n F hF]
    iintro %x ⟨_, Hcredit⟩
    twp_pure
    twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    twp_bind pl(&Occil.uniformSum #int (n : ℤ))
    iapply tglWp_wand
    isplitl [Hcredit]
    · isimp only [credit] at Hcredit
      iapply (ih (fun y => F (x + y)) (hF.comp (measurable_const.add measurable_id))) $$ Hcredit
    iintro %v ⟨%y, %hv, Hcredit⟩
    subst v
    twp_pures
    twp_value
    imodintro
    iexists (x + y)
    iframe Hcredit
    ipureintro
    exact Val.ext (by simp)

/-- Typed Irwin–Hall specification, including the zero-summand point mass. -/
theorem uniformSum_distSpec (E : CoPset) (n : ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.uniformSum #int (n : ℤ)) (law n) Val.real where
  spec F hF := wand_entails (twp_uniformSum E n F hF)

end specification

end

end SampLib.UniformSum
