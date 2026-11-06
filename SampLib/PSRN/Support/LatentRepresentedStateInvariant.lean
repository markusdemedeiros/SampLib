import SampLib.PSRN.Support.LatentRepresentedViews

/-! # Refinement-stable pure invariants alongside one physical view ownership -/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

def withInvariant (Q : S → Prop) (P : S → IProp GF) (s : S) : IProp GF := iprop(⌜Q s⌝ ∗ P s)

/-- A pure refinement invariant is retained without duplicating the physical world. -/
theorem represented_view_withInvariant (E : CoPset) (D : Model Ω S) (R : Representation D)
    (P : S → IProp GF) (handle : Val rT) (h : IsRepresentedViewSpec E D R P handle)
    (Q : S → Prop) (hQ : ∀ {s t}, D.refines s t → Q s → Q t) :
    IsRepresentedViewSpec E D R (withInvariant Q P) handle where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns, withInvariant] at Hstate
    icases Hstate with ⟨%hv, %hq, Hstate⟩
    subst v
    iapply (IsRepresentedViewSpec.wp h s n F hF _) $$ Hstate Hcredit
    iintro %t %I %hI Hstate Hcredit
    iexists t, I
    isplitl []
    · ipureintro
      exact ⟨rfl, hI⟩
    isplitl [Hstate]
    · isimp only [ViewOwns, withInvariant]
      isplitl []
      · ipureintro
        trivial
      isplitl []
      · ipureintro
        exact hQ hI.1 hq
      iexact Hstate
    iexact Hcredit

end

end SampLib.LatentReal
