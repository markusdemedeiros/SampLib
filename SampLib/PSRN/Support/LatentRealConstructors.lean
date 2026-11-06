import SampLib.PSRN.Support.LatentRationalScale
import SampLib.Core.Syntax.ClosedExp

/-! # Composing constructors for deferred real draws

A source constructor may already refine its posterior before returning. The mapped
constructor retains that refined state and all joint latent continuation credit.
-/

open ProbLang
open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

private instance negate_closed {rT : Type} : ClosedExp (Occil.PSRN.negate : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.PSRN.negate, Exp.fv]

private instance scale_closed {rT : Type} :
    ClosedExp (Occil.PSRN.scaleRational : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.PSRN.scaleRational, Exp.fv]

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- Negating a newly constructed oracle preserves its actual posterior refinement. -/
theorem negate_latentDistSpec (E : CoPset) (e : Exp rT) (D : Model Ω S) (initial : S)
    (owns : Val rT → S → IProp GF) (hsource : IsLatentDistSpec E e D initial owns) :
    IsLatentDistSpec E pl(let source := &e; &Occil.PSRN.negate source)
      D.negate initial (negateOwns owns) where
  oracle := negate_oracleSpec E D owns hsource.oracle
  spec F hF := by
    iintro Hcredit
    isimp only [Model.negate] at Hcredit
    twp_bind e
    iapply hsource.wp F hF _ $$ Hcredit
    iintro %source %t %ht Hstate Hcredit
    twp_pure
    isimp only [ClosedExp.openRec, ClosedExp.closeRec]
    iapply tglWp_wand
    isplitl [Hstate]
    · iapply twp_negate E owns source t $$ Hstate
    iintro %v Hstate
    iexists t
    isimp only [Model.negate]
    iframe Hstate Hcredit
    ipureintro
    exact ht

/-- Rational scaling composes with construction without observing the source. -/
theorem scaleRational_latentDistSpec (E : CoPset) (e : Exp rT) (D : Model Ω S)
    (initial : S) (owns : Val rT → S → IProp GF)
    (hsource : IsLatentDistSpec E e D initial owns) (a b : ℤ) (hb : 0 < b) :
    IsLatentDistSpec E pl(let source := &e; &Occil.PSRN.scaleRational source #a #b)
      (D.scale ((a : ℝ) / b)) initial (scaleRationalOwns owns a b) where
  oracle := scaleRational_oracleSpec E D owns hsource.oracle a b hb
  spec F hF := by
    iintro Hcredit
    isimp only [Model.scale] at Hcredit
    twp_bind e
    iapply hsource.wp F hF _ $$ Hcredit
    iintro %source %t %ht Hstate Hcredit
    twp_pure
    isimp only [ClosedExp.openRec, ClosedExp.closeRec]
    iapply tglWp_wand
    isplitl [Hstate]
    · iapply twp_scaleRational E owns source t a b hb $$ Hstate
    iintro %v Hstate
    iexists t
    isimp only [Model.scale]
    iframe Hstate Hcredit
    ipureintro
    exact ht

end

end SampLib.LatentReal
