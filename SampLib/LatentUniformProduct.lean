import SampLib.LatentUniformRoot
import SampLib.Distributions.LatentReal.UniformProduct

/-! # Observing independent uniform streams under one joint credit

Either coordinate may be read first. The other stream remains owned, and every
continuation still depends on both latent uniforms through the product posterior.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentUniformProduct

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Reading the left coordinate preserves both roots and the full joint continuation. -/
theorem twp_observe_left (E : CoPset) (l r : Loc) (p q : List Bool) (n : ℕ)
    (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    iprop(UniformBag.owns l p ∗ UniformBag.owns r q ∗ ↯ (∫⁻ z, F z ∂law p q)) ⊢
      tglWp E pl(&(LatentUniform.value (rT := rT) l).fst #int (n : ℤ))
        (fun result : Val rT => iprop(∃ p' : List Bool,
          ⌜UniformBag.readRefines p n p' ∧
            result = LatentReal.intervalVal (LatentUniform.interval p' n)⌝ ∗
          UniformBag.owns l p' ∗ UniformBag.owns r q ∗ ↯ (∫⁻ z, F z ∂law p' q))) := by
  have hread := LatentUniform.twp_observe_root (rT := rT) (GF := GF) E l p n
    (leftCredit q F) (measurable_leftCredit q hF)
  unfold DyadicPosterior.credit at hread
  iintro ⟨Hleft, Hright, Hcredit⟩
  isimp only [expectation_left p q F hF] at Hcredit
  iapply tglWp_wand
  isplitl [Hleft Hcredit]
  · iapply hread
    iframe Hleft Hcredit
  iintro %result ⟨%p', %hp, Hleft, Hcredit⟩
  isimp only [← expectation_left p' q F hF] at Hcredit
  iexists p'
  iframe Hleft Hright Hcredit
  ipureintro
  exact hp

/-- Reading the right coordinate uses the same joint law and retains the left cache. -/
theorem twp_observe_right (E : CoPset) (l r : Loc) (p q : List Bool) (n : ℕ)
    (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    iprop(UniformBag.owns l p ∗ UniformBag.owns r q ∗ ↯ (∫⁻ z, F z ∂law p q)) ⊢
      tglWp E pl(&(LatentUniform.value (rT := rT) r).fst #int (n : ℤ))
        (fun result : Val rT => iprop(∃ q' : List Bool,
          ⌜UniformBag.readRefines q n q' ∧
            result = LatentReal.intervalVal (LatentUniform.interval q' n)⌝ ∗
          UniformBag.owns l p ∗ UniformBag.owns r q' ∗ ↯ (∫⁻ z, F z ∂law p q'))) := by
  have hread := LatentUniform.twp_observe_root (rT := rT) (GF := GF) E r q n
    (rightCredit p F) (measurable_rightCredit p hF)
  unfold DyadicPosterior.credit at hread
  iintro ⟨Hleft, Hright, Hcredit⟩
  isimp only [expectation_right p q F hF] at Hcredit
  iapply tglWp_wand
  isplitl [Hright Hcredit]
  · iapply hread
    iframe Hright Hcredit
  iintro %result ⟨%q', %hq, Hright, Hcredit⟩
  isimp only [← expectation_right p q' F hF] at Hcredit
  iexists q'
  iframe Hleft Hright Hcredit
  ipureintro
  exact hq

end specification

end SampLib.LatentUniformProduct
