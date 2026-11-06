import SampLib.PSRN.Support.PSRNRoot
import SampLib.PSRN.Support.LatentDyadicRepresentation

/-! # Compositional constructor and observer specifications for deferred roots -/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.Root

noncomputable section

private instance root_closed {rT : Type} : ClosedExp (Occil.PSRN.root : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- The root closure retains its actual source and its current comparison domain. -/
def owns (D : Model Ω S) (degree : ℕ) (rawOwns : Val rT → S → IProp GF)
    (v : Val rT) (s : S) : IProp GF :=
  iprop(∃ source : Val rT, ⌜v = Program.value source degree ∧ Admissible D degree s⌝ ∗
    rawOwns source s)

/-- Every observation refines the same source and preserves all joint latent credit. -/
theorem representedOracleSpec (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (rawOwns : Val rT → S → IProp GF) (hsource : IsOracleSpec E D rawOwns)
    (degree : ℕ) (hdegree : 2 ≤ degree) :
    IsRepresentedOracleSpec E (D.nthRoot degree) (D.nthRoot degree).dyadicRepresentation
      (owns D degree rawOwns) where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [owns] at Hstate
    icases Hstate with ⟨%source, %hv, Hstate⟩
    rcases hv with ⟨rfl, hadmissible⟩
    isimp only [Model.nthRoot] at Hcredit
    iapply tglWp_wand
    isplitl [Hstate Hcredit]
    · iapply twp_observe E D hD (rawOwns source) source
        (hsource.viewSpec E D rawOwns source) degree hdegree s hadmissible n F hF
      iframe Hstate Hcredit
    iintro %result ⟨%t, %I, %hI, Hstate, Hcredit⟩
    iexists t, I
    isplit
    · ipureintro
      exact ⟨hI.1, hI.2.1, hI.2.2.1,
        (D.nthRoot degree).observed_dyadic_of_format t n I
          hI.2.2.2.1 hI.2.2.2.2.1
          (by simpa only [Model.nthRoot, Int.cast_pow] using hI.2.2.2.2.2)⟩
    isplitl [Hstate]
    · isimp only [owns]
      iexists source
      iframe Hstate
      ipureintro
      exact ⟨rfl, hadmissible.refines hI.2.1⟩
    isimp only [Model.nthRoot]
    iframe Hcredit

/-- Forgetting endpoint format gives the ordinary shared-oracle protocol. -/
theorem oracleSpec (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (rawOwns : Val rT → S → IProp GF) (hsource : IsOracleSpec E D rawOwns)
    (degree : ℕ) (hdegree : 2 ≤ degree) :
    IsOracleSpec E (D.nthRoot degree) (owns D degree rawOwns) :=
  (representedOracleSpec E D hD rawOwns hsource degree hdegree).forget

/-- The actual constructor composes with an admissible source sampler. -/
theorem latentDistSpec (E : CoPset) (e : Exp rT) (D : Model Ω S) (hD : D.MeasurableError)
    (initial : S) (rawOwns : Val rT → S → IProp GF)
    (hsource : IsLatentDistSpec E e D initial rawOwns)
    (degree : ℕ) (hdegree : 2 ≤ degree) (hadmissible : Admissible D degree initial) :
    IsLatentDistSpec E pl(let source := &e; &Occil.PSRN.root source #int (degree : ℤ))
      (D.nthRoot degree) initial (owns D degree rawOwns) where
  oracle := oracleSpec E D hD rawOwns hsource.oracle degree hdegree
  spec F hF := by
    iintro Hcredit
    isimp only [Model.nthRoot] at Hcredit
    twp_bind e
    iapply hsource.wp F hF _ $$ Hcredit
    iintro %source %t %ht Hstate Hcredit
    twp_pure
    isimp only [ClosedExp.openRec, ClosedExp.closeRec]
    iapply tglWp_wand
    isplitl [Hstate]
    · iapply Program.twp_root E source degree hdegree (rawOwns source) t $$ Hstate
    iintro %v Hstate
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨%hv, Hstate⟩
    subst v
    iexists t
    isplit
    · ipureintro
      exact ht
    isplitl [Hstate]
    · isimp only [owns]
      iexists source
      iframe Hstate
      ipureintro
      exact ⟨rfl, hadmissible.refines ht⟩
    isimp only [Model.nthRoot]
    iframe Hcredit

/-- The constructor also provides its exact, reusable dyadic interval representation. -/
theorem representedDistSpec (E : CoPset) (e : Exp rT) (D : Model Ω S)
    (hD : D.MeasurableError) (initial : S) (rawOwns : Val rT → S → IProp GF)
    (hsource : IsLatentDistSpec E e D initial rawOwns)
    (degree : ℕ) (hdegree : 2 ≤ degree) (hadmissible : Admissible D degree initial) :
    IsRepresentedDistSpec E pl(let source := &e; &Occil.PSRN.root source #int (degree : ℤ))
      (D.nthRoot degree) (D.nthRoot degree).dyadicRepresentation initial
      (owns D degree rawOwns) where
  spec := (latentDistSpec E e D hD initial rawOwns hsource degree hdegree hadmissible).spec
  oracle := representedOracleSpec E D hD rawOwns hsource.oracle degree hdegree

end specification

end

end SampLib.LatentReal.Root
