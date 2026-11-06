import SampLib.PSRN.Support.LatentNormalizedCoordinates
import SampLib.PSRN.Support.LatentDivideCoordinates

/-! # Actual shared-sum normalization of a family of lazy handles -/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.Normalization

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω] {n : ℕ}
local bi (IProp GF)

/-- Both normalizing constructors use this identical local sum and quotient family. -/
theorem twp_constructor (E : CoPset) (D : Model Ω S) (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i))
    (P : (Fin n → Val rT) → S → IProp GF) (original : Fin n → Val rT) (s : S)
    (hnonzero : RepresentedReciprocalView.Nonzero (denominator D views hviews) s) :
    P original s ⊢
      tglWp E pl(&Occil.PSRN.divideCoordinates &(vectorVal original).fst
        (&CoordinateSum.source &(vectorVal original).fst))
        (fun v => VectorOwns (owns D views hviews P) v s) := by
  iintro Hstate
  twp_bind pl(&CoordinateSum.source &(vectorVal original).fst)
  iapply tglWp_wand
  isplitl [Hstate]
  · iapply CoordinateSum.twp_sum E original (P original) s $$ Hstate
  iintro %sum Hstate
  isimp only [ViewOwns] at Hstate
  icases Hstate with ⟨%hsum, Hstate⟩
  subst sum
  simp only [Exp.ofVal]
  iapply tglWp_wand
  isplitl [Hstate]
  · iapply DivideCoordinates.twp_constructor E (denominator D views hviews)
      (P original) original (CoordinateSum.value original) s
    isimp only [withInvariant]
    iframe Hstate
    ipureintro
    exact hnonzero
  iintro %output Hstate
  isimp only [ViewOwns] at Hstate
  icases Hstate with ⟨%hout, Hstate⟩
  subst output
  isimp only [VectorOwns, owns]
  iexists handles original
  isplitl []
  · ipureintro
    rfl
  iexists original
  isplitl []
  · ipureintro
    rfl
  iexact Hstate

end

end SampLib.LatentReal.Normalization
