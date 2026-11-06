import SampLib.LatentViews
import SampLib.LatentRationalScale

/-! # Unary arithmetic views retaining their fixed source handle -/

open ProbLang

namespace SampLib.LatentReal

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- Negation is another view of the same owned state, including aliases. -/
theorem negate_viewSpec (E : CoPset) (D : Model Ω S) (P : S → IProp GF)
    (source : Val rT) (hsource : IsViewSpec E D P source) :
    IsViewSpec E D.negate P (negateVal source) where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨%hv, Hstate⟩
    subst v
    iapply tglWp_wand
    isplitl [Hstate Hcredit]
    · iapply (negate_oracleSpec E D (ViewOwns source P) hsource).observe
        (negateVal source) s n F hF
      isplitl [Hstate]
      · isimp only [negateOwns, ViewOwns]
        iexists source
        iframe Hstate
        itrivial
      iexact Hcredit
    iintro %result ⟨%t, %I, %hI, Hstate, Hcredit⟩
    rcases hI with ⟨rfl, hrefines, hencloses⟩
    isimp only [negateOwns, ViewOwns] at Hstate
    icases Hstate with ⟨%original, _, %heq, Hstate⟩
    iexists t, I
    isplit
    · ipureintro
      exact ⟨rfl, hrefines, hencloses⟩
    isplitl [Hstate]
    · isimp only [ViewOwns]
      iframe Hstate
    iexact Hcredit

/-- Signed rational scaling shares its source's physical ownership and full joint law. -/
theorem scaleRational_viewSpec (E : CoPset) (D : Model Ω S) (P : S → IProp GF)
    (source : Val rT) (hsource : IsViewSpec E D P source) (a b : ℤ) (hb : 0 < b) :
    IsViewSpec E (D.scale ((a : ℝ) / b)) P (scaleRationalVal source a b) where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨%hv, Hstate⟩
    subst v
    iapply tglWp_wand
    isplitl [Hstate Hcredit]
    · iapply (scaleRational_oracleSpec E D (ViewOwns source P) hsource a b hb).observe
        (scaleRationalVal source a b) s n F hF
      isplitl [Hstate]
      · isimp only [scaleRationalOwns, ViewOwns]
        iexists source
        iframe Hstate
        itrivial
      iexact Hcredit
    iintro %result ⟨%t, %I, %hI, Hstate, Hcredit⟩
    rcases hI with ⟨rfl, hrefines, hencloses⟩
    isimp only [scaleRationalOwns, ViewOwns] at Hstate
    icases Hstate with ⟨%original, _, %heq, Hstate⟩
    iexists t, I
    isplit
    · ipureintro
      exact ⟨rfl, hrefines, hencloses⟩
    isplitl [Hstate]
    · isimp only [ViewOwns]
      iframe Hstate
    iexact Hcredit

end

end SampLib.LatentReal
