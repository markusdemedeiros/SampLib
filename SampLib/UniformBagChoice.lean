import SampLib.UniformBagBracket

/-! # Conditional choice after a shared-uniform comparison

The selected continuation retains the original bag, its refined posterior
credit, and the almost-everywhere comparison fact.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.UniformBag

noncomputable section

/-- Choose a continuation by comparing the cached uniform with one rational threshold. -/
def choice {rT : Type} (l : Loc) (numerator denominator : ℤ)
    (yes no : Exp rT) : Exp rT :=
  .cond pl(&Occil.uniformBagLess #loc l #int numerator #int denominator) yes no

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Arbitrary branches compose under the updated cache and its conditional credit. -/
theorem twp_choice (E : CoPset) (l : Loc) (p : List Bool) (numerator denominator : ℤ)
    (hd : 0 < denominator) (G : ℝ → ℝ≥0∞) (hG : Measurable G)
    (yes no : Exp rT) (Φ : Val rT → IProp GF)
    (hyes : ∀ q : List Bool, p <+: q →
      DyadicPosterior.resolves q ((numerator : ℝ) / denominator) true →
      iprop(owns l q ∗ ↯ (DyadicPosterior.credit q G)) ⊢ tglWp E yes Φ)
    (hno : ∀ q : List Bool, p <+: q →
      DyadicPosterior.resolves q ((numerator : ℝ) / denominator) false →
      iprop(owns l q ∗ ↯ (DyadicPosterior.credit q G)) ⊢ tglWp E no Φ) :
    iprop(owns l p ∗ ↯ (DyadicPosterior.credit p G)) ⊢
      tglWp E (choice l numerator denominator yes no) Φ := by
  iintro ⟨Hbag, Hcredit⟩
  isimp only [choice]
  twp_bind pl(&Occil.uniformBagLess #loc l #int numerator #int denominator)
  iapply tglWp_wand
  isplitl [Hbag Hcredit]
  · iapply twp_uniformBagLess E l p numerator denominator hd G hG
    iframe Hbag Hcredit
  iintro %v Hnext
  isimp only [lessPost] at Hnext
  ihave ⟨%b, %q, %hq, Hbag, Hcredit⟩ := Hnext
  rcases hq with ⟨rfl, hprefix, hcmp⟩
  cases b
  · twp_pure
    iapply hno q hprefix hcmp
    iframe Hbag Hcredit
  · twp_pure
    iapply hyes q hprefix hcmp
    iframe Hbag Hcredit

end specification

end

end SampLib.UniformBag
