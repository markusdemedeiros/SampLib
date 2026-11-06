import SampLib.PSRN.Support.LatentRoot

/-! # Root and source views sharing one admissible physical state -/

open ProbLang

namespace SampLib.LatentReal.Root

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω]

theorem sameWorld (D : Model Ω S) (degree : ℕ) : D.SameWorld (D.nthRoot degree) :=
  ⟨fun _ => rfl, fun _ _ => Iff.rfl⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The domain is a persistent fact about the current cache; physical ownership occurs once. -/
def admissibleState (D : Model Ω S) (degree : ℕ) (P : S → IProp GF) (s : S) : IProp GF :=
  iprop(⌜Admissible D degree s⌝ ∗ P s)

/-- The original source remains a view under the same strengthened ownership as its root. -/
theorem source_viewSpec (E : CoPset) (D : Model Ω S) (degree : ℕ) (P : S → IProp GF)
    (source : Val rT) (hsource : IsViewSpec E D P source) :
    IsViewSpec E D (admissibleState D degree P) source where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns, admissibleState] at Hstate
    icases Hstate with ⟨%hv, %hadmissible, Hstate⟩
    subst v
    iapply hsource.wp s n F hF _ $$ Hstate Hcredit
    iintro %t %I %hI Hstate Hcredit
    iexists t, I
    isplit
    · ipureintro
      exact ⟨rfl, hI⟩
    isplitl [Hstate]
    · isimp only [ViewOwns, admissibleState]
      isplit
      · itrivial
      isplit
      · ipureintro
        exact hadmissible.refines hI.1
      · iframe Hstate
    iexact Hcredit

/-- A source representation is retained under the same pure comparison-domain guard. -/
theorem represented_source_viewSpec (E : CoPset) (D : Model Ω S) (R : Representation D)
    (degree : ℕ) (P : S → IProp GF) (source : Val rT)
    (hsource : IsRepresentedViewSpec E D R P source) :
    IsRepresentedViewSpec E D R (admissibleState D degree P) source where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns, admissibleState] at Hstate
    icases Hstate with ⟨%hv, %hadmissible, Hstate⟩
    subst v
    iapply tglWp_wand
    isplitl [Hstate Hcredit]
    · iapply hsource.observe source s n F hF
      isplitl [Hstate]
      · isimp only [ViewOwns]
        iframe Hstate
      iexact Hcredit
    iintro %result ⟨%t, %I, %hI, Hstate, Hcredit⟩
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨_, Hstate⟩
    iexists t, I
    isplit
    · ipureintro
      exact hI
    isplitl [Hstate]
    · isimp only [ViewOwns, admissibleState]
      isplit
      · itrivial
      isplit
      · ipureintro
        exact hadmissible.refines hI.2.1
      · iframe Hstate
    iexact Hcredit

/-- The fixed root handle shares the source's physical state and full latent world. -/
theorem represented_viewSpec (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (P : S → IProp GF) (source : Val rT) (hsource : IsViewSpec E D P source)
    (degree : ℕ) (hdegree : 2 ≤ degree) :
    IsRepresentedViewSpec E (D.nthRoot degree) (D.nthRoot degree).dyadicRepresentation
      (admissibleState D degree P) (Program.value source degree) where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns, admissibleState] at Hstate
    icases Hstate with ⟨%hv, %hadmissible, Hstate⟩
    subst v
    iapply tglWp_wand
    isplitl [Hstate Hcredit]
    · iapply (representedOracleSpec E D hD (ViewOwns source P) hsource degree hdegree).observe
        (Program.value source degree) s n F hF
      isplitl [Hstate]
      · isimp only [owns, ViewOwns]
        iexists source
        isplit
        · ipureintro
          exact ⟨rfl, hadmissible⟩
        iframe Hstate
        itrivial
      iexact Hcredit
    iintro %result ⟨%t, %I, %hI, Hstate, Hcredit⟩
    isimp only [owns, ViewOwns] at Hstate
    icases Hstate with ⟨%original, %horiginal, %hsourceVal, Hstate⟩
    subst original
    iexists t, I
    isplit
    · ipureintro
      exact hI
    isplitl [Hstate]
    · isimp only [ViewOwns, admissibleState]
      isplit
      · itrivial
      isplit
      · ipureintro
        exact horiginal.2
      · iframe Hstate
    iexact Hcredit

/-- The fixed root also satisfies the ordinary shared-view protocol. -/
theorem viewSpec (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (P : S → IProp GF) (source : Val rT) (hsource : IsViewSpec E D P source)
    (degree : ℕ) (hdegree : 2 ≤ degree) :
    IsViewSpec E (D.nthRoot degree) (admissibleState D degree P) (Program.value source degree) :=
  (represented_viewSpec E D hD P source hsource degree hdegree).forget

end specification

end

end SampLib.LatentReal.Root
