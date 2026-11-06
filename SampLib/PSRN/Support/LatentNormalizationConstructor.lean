import SampLib.PSRN.Support.LatentNormalizationModel
import SampLib.PSRN.Support.LatentRepresentedVectorSpec
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

def handles (original : Fin n → Val rT) : Fin n → Val rT :=
  fun i => RepresentedDivision.value (original i) (CoordinateSum.value original)

/-- The original family is existentially retained, together with one nonzero sum. -/
def owns (D : Model Ω S) (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i))
    (P : (Fin n → Val rT) → S → IProp GF) (output : Fin n → Val rT) (s : S) : IProp GF :=
  iprop(∃ original : Fin n → Val rT, ⌜output = handles original⌝ ∗
    withInvariant (RepresentedReciprocalView.Nonzero (denominator D views hviews))
      (P original) s)

/-- Every quotient observes the common normalizer under the same family ownership. -/
theorem coordinateSpec (E : CoPset) (D : Model Ω S) (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) (Rs : ∀ i, Representation (views i))
    (P : (Fin n → Val rT) → S → IProp GF)
    (hcoord : ∀ original i, IsRepresentedViewSpec E (views i) (Rs i) (P original) (original i))
    (output : Fin n → Val rT) (i : Fin n) :
    IsRepresentedViewSpec E (coordinate D views hviews Rs i)
      (representation D views hviews Rs i) (owns D views hviews P output) (output i) where
  observe v s k F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns, owns] at Hstate
    icases Hstate with ⟨%hv, %original, %ho, Hstate⟩
    subst output
    subst v
    have hsum := CoordinateSum.represented_oracleSpec E D views hviews Rs original
      (P original) (hcoord original)
    have hquot : IsRepresentedViewSpec E (coordinate D views hviews Rs i)
        (representation D views hviews Rs i)
        (withInvariant (RepresentedReciprocalView.Nonzero (denominator D views hviews))
          (P original)) (handles original i) := RepresentedDivision.viewSpec E (views i) (denominator D views hviews)
      ((hviews i).between (CoordinateSum.sameWorld D views hviews)) (Rs i)
      (denominatorRepresentation D views hviews Rs) (P original) (original i)
      (CoordinateSum.value original) (hcoord original i) hsum
    iapply hquot.wp s k F hF _ $$ Hstate Hcredit
    iintro %t %I %hI Hstate Hcredit
    iexists t, I
    isplitl []
    · ipureintro
      exact ⟨rfl, hI⟩
    isplitl [Hstate]
    · isimp only [ViewOwns, owns]
      isplitl []
      · ipureintro
        trivial
      iexists original
      isplitl []
      · ipureintro
        rfl
      iexact Hstate
    iexact Hcredit

end

end SampLib.LatentReal.Normalization

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
