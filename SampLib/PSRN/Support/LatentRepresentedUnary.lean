import SampLib.PSRN.Support.LatentRepresentedTranslate
import SampLib.PSRN.Support.LatentRealMap

/-! # Represented unary views of one owned world -/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

namespace Representation

variable {Ω S : Type} [MeasurableSpace Ω]

def negate (D : Model Ω S) (R : Representation D) : Representation D.negate where
  interval n x := (R.interval n x).negate
  measurable_lower n := (R.measurable_upper n).neg
  measurable_upper n := (R.measurable_lower n).neg
  measurable_denominator n := R.measurable_denominator n
  approximates s := (R.approximates s).mono fun _ hx => hx.negate

theorem observed_negate (D : Model Ω S) (R : Representation D)
    {s : S} {n : ℕ} {I : RationalInterval} (hI : R.Observed s n I) :
    (negate D R).Observed s n I.negate :=
  hI.mono fun _ hx => congrArg RationalInterval.negate hx

end Representation

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- A fixed alias keeps exactly the original oracle's physical ownership. -/
theorem IsRepresentedOracleSpec.viewSpec {E : CoPset} {D : Model Ω S}
    {R : Representation D} {owns : Val rT → S → IProp GF}
    (h : IsRepresentedOracleSpec E D R owns) (handle : Val rT) :
    IsRepresentedViewSpec E D R (owns handle) handle where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨%hv, Hstate⟩
    subst v
    iapply tglWp_wand
    isplitl [Hstate Hcredit]
    · iapply h.observe handle s n F hF
      iframe Hstate Hcredit
    iintro %result ⟨%t, %I, %hI, Hstate, Hcredit⟩
    iexists t, I
    iframe Hcredit
    isplitl []
    · ipureintro
      exact hI
    isimp only [ViewOwns]
    iframe Hstate

/-- The pure negation constructor captures the fixed handle without observing it. -/
theorem twp_negate_view (E : CoPset) (source : Val rT) (P : S → IProp GF) (s : S) :
    P s ⊢ tglWp E pl(&Occil.PSRN.negate &source.fst)
      (fun v => ViewOwns (negateVal source) P v s) := by
  iintro Hstate
  iapply tglWp_wand
  isplitl [Hstate]
  · iapply twp_negate E (ViewOwns source P) source s
    isimp only [ViewOwns]
    iframe Hstate
  iintro %v Hstate
  isimp only [negateOwns, ViewOwns] at Hstate
  icases Hstate with ⟨%original, %hv, %heq, Hstate⟩
  subst original
  isimp only [ViewOwns]
  iframe Hstate
  ipureintro
  exact hv

/-- Negation reads the fixed source and retains its actual reflected interval. -/
theorem represented_negate_viewSpec (E : CoPset) (D : Model Ω S) (R : Representation D)
    (P : S → IProp GF) (source : Val rT) (hsource : IsRepresentedViewSpec E D R P source) :
    IsRepresentedViewSpec E D.negate (Representation.negate D R) P (negateVal source) where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨%hv, Hstate⟩
    subst v
    twp_pures
    twp_bind pl(&source.fst #int (n : ℤ))
    isimp only [Model.negate] at Hcredit
    iapply hsource.wp s n F hF _ $$ Hstate Hcredit
    iintro %t %I %hI Hstate Hcredit
    twp_pures
    twp_value
    imodintro
    iexists t, I.negate
    isplit
    · ipureintro
      refine ⟨?_, hI.1, D.encloses_negate hI.2.1,
        Representation.observed_negate D R hI.2.2⟩
      apply Val.ext
      rfl
    isplitl [Hstate]
    · isimp only [ViewOwns]
      iframe Hstate
    isimp only [Model.negate]
    iexact Hcredit

/-- Rational translation retains a fixed handle's one shared world resource. -/
theorem represented_translate_viewSpec (E : CoPset) (D : Model Ω S) (R : Representation D)
    (P : S → IProp GF) (source : Val rT) (hsource : IsRepresentedViewSpec E D R P source)
    (a b : ℤ) (hb : 0 < b) :
    IsRepresentedViewSpec E (D.translate ((a : ℝ) / b)) (Representation.translate D R a b hb)
      P (translateVal source a b) where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨%hv, Hstate⟩
    subst v
    iapply tglWp_wand
    isplitl [Hstate Hcredit]
    · iapply (represented_translate_oracleSpec E D R (ViewOwns source P) hsource a b hb).observe
        (translateVal source a b) s n F hF
      isplitl [Hstate]
      · isimp only [translateOwns, ViewOwns]
        iexists source
        iframe Hstate
        itrivial
      iexact Hcredit
    iintro %result ⟨%t, %I, %hI, Hstate, Hcredit⟩
    isimp only [translateOwns, ViewOwns] at Hstate
    icases Hstate with ⟨%original, _, %heq, Hstate⟩
    iexists t, I
    isplit
    · ipureintro
      exact hI
    isplitl [Hstate]
    · isimp only [ViewOwns]
      iframe Hstate
    iexact Hcredit

end specification

end

end SampLib.LatentReal
