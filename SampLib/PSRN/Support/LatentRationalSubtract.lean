import SampLib.Latent.LatentViews
import SampLib.PSRN.Support.LatentRationalScale
import SampLib.PSRN.Support.LatentConstantView
import SampLib.PSRN.Support.LatentAddition
import SampLib.Latent.LatentViews
import SampLib.Latent.Laws.MeasuredError
import SampLib.Core.Syntax.ClosedExp

/-! # Subtracting a fixed rational on the right of a deferred real

The actual source constructs a rational oracle, negates it, then adds it to the
original handle. These cache-free constant views retain one shared ownership.
-/

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

open ProbLang
open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

namespace Model

variable {Ω S : Type} [MeasurableSpace Ω]

/-- The source and its negated constant use the same underlying world. -/
theorem sameWorld_negate_constant (D : Model Ω S) (c : ℝ) :
    D.SameWorld (D.constant c).negate := ⟨fun _ => rfl, fun _ _ => Iff.rfl⟩

/-- Right-rational subtraction retains the source posterior and its error envelope. -/
def subtractRational (D : Model Ω S) (a b : ℤ) : Model Ω S :=
  D.add (D.constant ((a : ℝ) / b)).negate (D.sameWorld_negate_constant _)

@[simp] theorem subtractRational_value (D : Model Ω S) (a b : ℤ) (x : Ω) :
    (D.subtractRational a b).value x = D.value x - (a : ℝ) / b := by
  simp [subtractRational, add, constant, negate, sub_eq_add_neg]

@[simp] theorem subtractRational_error (D : Model Ω S) (a b : ℤ) (n : ℕ) (x : Ω) :
    (D.subtractRational a b).error n x = D.error n x := by
  simp [subtractRational, add, constant, negate]

theorem MeasurableError.subtractRational {D : Model Ω S} (hD : D.MeasurableError) (a b : ℤ) :
    (D.subtractRational a b).MeasurableError := by
  intro n
  rw [show (D.subtractRational a b).error n = D.error n from
    funext (subtractRational_error D a b n)]
  exact hD n

end Model

/-- The actual closure returned by subtracting a constructed right rational. -/
def subtractRationalVal {rT : Type} (source : Val rT) (a b : ℤ) : Val rT :=
  addVal source (negateVal (LatentRational.value a b))

private instance add_closed {rT : Type} : ClosedExp (Occil.PSRN.add : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.PSRN.add, Exp.fv]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- Constructing right subtraction preserves the original fixed source state. -/
theorem twp_subtractRational (E : CoPset) (source : Val rT) (a b : ℤ) (hb : 0 < b)
    (P : S → IProp GF) (s : S) :
    iprop(P s) ⊢
      tglWp E pl(&Occil.PSRN.subtract &source.fst (&Occil.PSRN.rational #a #b))
        (fun v => ViewOwns (subtractRationalVal source a b) P v s) := by
  iintro Hstate
  twp_bind pl(&Occil.PSRN.rational #a #b)
  twp_pures
  rw [decide_eq_false (not_le.mpr hb)]
  twp_pures
  twp_value
  imodintro
  iterate 2 twp_pure
  isimp only [ClosedExp.openRec, ClosedExp.closeRec]
  twp_bind pl(&Occil.PSRN.negate &(LatentRational.value a b).fst)
  twp_pures
  twp_value
  imodintro
  ieval (
    change _ ⊢ tglWp E
      pl(&Occil.PSRN.add &source.fst &(negateVal (LatentRational.value a b)).fst) _)
  isimp only [subtractRationalVal]
  iapply twp_add E source (negateVal (LatentRational.value a b)) P s $$ Hstate

/-- Right subtraction observes the source once and threads the same joint ownership. -/
theorem subtractRational_viewSpec (E : CoPset) (D : Model Ω S) (P : S → IProp GF)
    (source : Val rT) (hsource : IsViewSpec E D P source) (a b : ℤ) (hb : 0 < b) :
    IsViewSpec E (D.subtractRational a b) P (subtractRationalVal source a b) :=
  add_oracleSpec E D (D.constant ((a : ℝ) / b)).negate (D.sameWorld_negate_constant _)
    P source (negateVal (LatentRational.value a b)) hsource
    (negate_viewSpec E (D.constant ((a : ℝ) / b)) P (LatentRational.value a b)
      (constant_viewSpec E D P a b hb))

end specification

end

end SampLib.LatentReal
