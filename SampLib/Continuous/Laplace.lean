import SampLib.Continuous.Exponential
import SampLib.Uniform.FairCoin
import SampLib.Continuous.Laws.Laplace

/-! # Laplace sampling by an independent exponential magnitude and fair sign -/

open Set ProbLang
open scoped ENNReal

namespace SampLib.Laplace

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangDist.IsUniformInt ℝ]
  [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

/-- CTE composition of exponential magnitude and a fresh fair sign. -/
theorem twp_laplace (E : CoPset)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ⊢ ↯ (∫⁻ z, F z ∂law) -∗ tglWp E pl(&Occil.laplace #())
      (fun v : Val ℝ => iprop(∃ z : ℝ, ⌜v = Val.real z⌝ ∗ ↯ (F z))) := by
  have hexp := Exponential.exponential_distSpec (GF := GF) E
  dsimp only [Exponential.law] at hexp
  iintro Hcredit
  twp_pure
  simp only [Exponential.exponential_closeRec, Exponential.exponential_openRec]
  twp_bind pl(&Occil.exponential #())
  isimp only [← expectation_preservation F hF] at Hcredit
  iapply (hexp.wp (credit F) (measurable_credit F hF) _) $$ Hcredit
  iintro %x Hcredit
  twp_pure
  twp_bind pl(&Occil.fairCoin #())
  isimp only [credit] at Hcredit
  iapply ((FairCoin.fairCoin_distSpec E).wp (fun b => F (if b then x else -x))
    (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  cases b <;> twp_pures <;> twp_value <;> imodintro
  · iexists (-x)
    isimp only [Bool.false_eq_true, ite_false] at Hcredit
    iframe Hcredit
    ipureintro
    exact Val.ext (by simp)
  · iexists x
    isimp only [ite_true] at Hcredit
    iframe Hcredit
    itrivial

/-- Typed standard Laplace specification. -/
theorem laplace_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.laplace #()) law Val.real where
  spec F hF := wand_entails (twp_laplace E F hF)

end specification

end

end SampLib.Laplace
