import SampLib.PSRN.Support.Represented.Addition
import SampLib.PSRN.Support.Arithmetic.RationalTranslate

/-! # Represented rational translation

A rational point adds no uncertainty. The translated oracle reads the same
source handle and returns exactly the point interval added to its observation.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

namespace Representation

variable {Ω S : Type} [MeasurableSpace Ω]

/-- Translation keeps the actual source interval schedule, including coarse observations. -/
def translate (D : Model Ω S) (R : Representation D) (a b : ℤ) (hb : 0 < b) :
    Representation (D.translate ((a : ℝ) / b)) where
  interval n x := (RationalInterval.point a b hb).add (R.interval n x)
  measurable_lower n := by
    exact (measurable_const.mul (R.measurable_denominator n)).add
      ((R.measurable_lower n).mul_const b)
  measurable_upper n := by
    exact (measurable_const.mul (R.measurable_denominator n)).add
      ((R.measurable_upper n).mul_const b)
  measurable_denominator n := measurable_const.mul (R.measurable_denominator n)
  approximates s := by
    filter_upwards [(Representation.constant D a b hb).approximates s, R.approximates s]
      with x hc hx
    exact hc.add hx

theorem observed_translate (D : Model Ω S) (R : Representation D) (a b : ℤ) (hb : 0 < b)
    {s : S} {n : ℕ} {I : RationalInterval} (hI : R.Observed s n I) :
    (translate D R a b hb).Observed s n ((RationalInterval.point a b hb).add I) := by
  filter_upwards [hI] with x hx
  exact congrArg (fun J => (RationalInterval.point a b hb).add J) hx

end Representation

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- Each translated query retains the exact source schedule and full joint credit. -/
theorem represented_translate_oracleSpec (E : CoPset) (D : Model Ω S) (R : Representation D)
    (owns : Val rT → S → IProp GF) (hsource : IsRepresentedOracleSpec E D R owns)
    (a b : ℤ) (hb : 0 < b) :
    IsRepresentedOracleSpec E (D.translate ((a : ℝ) / b)) (R.translate D a b hb)
      (translateOwns owns a b) where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [translateOwns] at Hstate
    icases Hstate with ⟨%source, %hv, Hstate⟩
    subst v
    twp_pures
    twp_bind pl(&source.fst #int (n : ℤ))
    isimp only [Model.translate] at Hcredit
    iapply hsource.wp source s n F hF _ $$ Hstate Hcredit
    iintro %t %I %hI Hstate Hcredit
    twp_pures
    twp_value
    imodintro
    iexists t, (RationalInterval.point a b hb).add I
    isplit
    · ipureintro
      refine ⟨?_, hI.1, D.encloses_translate hI.2.1 a b hb,
        R.observed_translate D a b hb hI.2.2⟩
      apply Val.ext
      simp [intervalVal, RationalInterval.add, RationalInterval.point, Exp.ofVal]
    isplitl [Hstate]
    · isimp only [translateOwns]
      iexists source
      iframe Hstate
      itrivial
    isimp only [Model.translate]
    iexact Hcredit

end specification

end

end SampLib.LatentReal
