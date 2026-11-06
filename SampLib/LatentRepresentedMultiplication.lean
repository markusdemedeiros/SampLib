import SampLib.LatentRepresentedViews
import SampLib.LatentMultiplication

/-! # Represented multiplication over one owned latent world

The two handles may alias. Sequential reads retain one world resource, and the
second refinement preserves the first interval's deterministic certificate.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

namespace Representation

variable {Ω S : Type} [MeasurableSpace Ω]

/-- The actual four-corner interval product at the same latent point. -/
def multiply (L R : Model Ω S) (hworld : L.SameWorld R)
    (left : Representation L) (right : Representation R) :
    Representation (L.multiply R hworld) where
  interval n x := (left.interval n x).multiply (right.interval n x)
  measurable_lower n := by
    exact (((left.measurable_lower n).mul (right.measurable_lower n)).min
      ((left.measurable_lower n).mul (right.measurable_upper n))).min
        (((left.measurable_upper n).mul (right.measurable_lower n)).min
          ((left.measurable_upper n).mul (right.measurable_upper n)))
  measurable_upper n := by
    exact (((left.measurable_lower n).mul (right.measurable_lower n)).max
      ((left.measurable_lower n).mul (right.measurable_upper n))).max
        (((left.measurable_upper n).mul (right.measurable_lower n)).max
          ((left.measurable_upper n).mul (right.measurable_upper n)))
  measurable_denominator n :=
    (left.measurable_denominator n).mul (right.measurable_denominator n)
  approximates s := by
    have hr := right.approximates s
    rw [hworld.posterior_eq s] at hr
    filter_upwards [left.approximates s, hr] with x hx hy
    exact hx.multiply hy

/-- Refinement retains both actual factors before forming their four-corner product. -/
theorem observed_multiply (L R : Model Ω S) (hworld : L.SameWorld R)
    (left : Representation L) (right : Representation R) {s t : S} (hst : L.refines s t)
    {n : ℕ} {I J : RationalInterval} (hI : left.Observed s n I) (hJ : right.Observed t n J) :
    (multiply L R hworld left right).Observed t n (I.multiply J) := by
  have hJ' : ∀ᵐ x ∂L.posterior t, J = right.interval n x := by
    simpa only [Observed, hworld.posterior_eq t] using hJ
  filter_upwards [left.observed_refines hst hI, hJ'] with x hx hy
  exact congrArg₂ RationalInterval.multiply hx hy

end Representation

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- The existing multiplication closure preserves both exact operand certificates. -/
theorem represented_multiply_oracleSpec (E : CoPset) (L R : Model Ω S)
    (hworld : L.SameWorld R) (leftRepr : Representation L) (rightRepr : Representation R)
    (P : S → IProp GF) (left right : Val rT)
    (hleft : IsRepresentedViewSpec E L leftRepr P left)
    (hright : IsRepresentedViewSpec E R rightRepr P right) :
    IsRepresentedViewSpec E (L.multiply R hworld)
      (Representation.multiply L R hworld leftRepr rightRepr) P (multiplyVal left right) where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨%hv, Hstate⟩
    subst v
    twp_pures
    twp_bind pl(&left.fst #int (n : ℤ))
    isimp only [Model.multiply] at Hcredit
    iapply hleft.wp s n F hF _ $$ Hstate Hcredit
    iintro %t %I %hI Hstate Hcredit
    twp_pures
    twp_bind pl(&right.fst #int (n : ℤ))
    isimp only [← hworld.posterior_eq t] at Hcredit
    iapply hright.wp t n F hF _ $$ Hstate Hcredit
    iintro %u %J %hJ Hstate Hcredit
    twp_pures
    twp_bind (intMaxCond _ _)
    iapply twp_intMax E _ _ _
    twp_pures
    twp_bind (intMaxCond _ _)
    iapply twp_intMax E _ _ _
    twp_pures
    twp_bind (intMaxCond _ _)
    iapply twp_intMax E _ _ _
    twp_pures
    twp_bind (intMinCond _ _)
    iapply twp_intMin E _ _ _
    twp_pures
    twp_bind (intMinCond _ _)
    iapply twp_intMin E _ _ _
    twp_pures
    twp_bind (intMinCond _ _)
    iapply twp_intMin E _ _ _
    twp_value
    imodintro
    have htu := (hworld.refines_iff t u).mp hJ.1
    iexists u, I.multiply J
    isplit
    · ipureintro
      refine ⟨?_, L.refines_trans hI.1 htu,
        L.encloses_multiply R hworld (L.encloses_refines htu hI.2.1) hJ.2.1,
        Representation.observed_multiply L R hworld leftRepr rightRepr htu hI.2.2 hJ.2.2⟩
      apply Val.ext
      simp [intervalVal, RationalInterval.multiply, Exp.ofVal, min_def, max_def]
    isplitl [Hstate]
    · isimp only [ViewOwns]
      iframe Hstate
    isimp only [hworld.posterior_eq u] at Hcredit
    isimp only [Model.multiply]
    iexact Hcredit

end specification

end

end SampLib.LatentReal
