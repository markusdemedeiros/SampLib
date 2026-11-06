import SampLib.PSRN.Support.LatentRepresentedViews
import SampLib.PSRN.Support.LatentConstantView
import SampLib.PSRN.Support.LatentAddition

/-! # Exact interval representations for constants and shared addition -/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

namespace Representation

variable {Ω S : Type} [MeasurableSpace Ω]

/-- A rational constant has the same exact interval at every precision. -/
def point (D : Model Ω S) (c : ℝ) (a b : ℤ) (hb : 0 < b) (hc : c = (a : ℝ) / b) :
    Representation (D.constant c) where
  interval _ _ := RationalInterval.point a b hb
  measurable_lower _ := measurable_const
  measurable_upper _ := measurable_const
  measurable_denominator _ := measurable_const
  approximates _ := Filter.Eventually.of_forall fun _ => by
    refine ⟨fun _ => (RationalInterval.contains_point _ _ _ _).mpr hc, ?_⟩
    simp [RationalInterval.width, RationalInterval.lowerReal, RationalInterval.upperReal,
      RationalInterval.point]

def constant (D : Model Ω S) (a b : ℤ) (hb : 0 < b) :
    Representation (D.constant ((a : ℝ) / b)) := point D _ a b hb rfl

/-- Both intervals are computed from the same latent point, even for aliases. -/
def add (L R : Model Ω S) (hworld : L.SameWorld R)
    (left : Representation L) (right : Representation R) : Representation (L.add R hworld) where
  interval n x := (left.interval n x).add (right.interval n x)
  measurable_lower n := by
    exact ((left.measurable_lower n).mul (right.measurable_denominator n)).add
      ((right.measurable_lower n).mul (left.measurable_denominator n))
  measurable_upper n := by
    exact ((left.measurable_upper n).mul (right.measurable_denominator n)).add
      ((right.measurable_upper n).mul (left.measurable_denominator n))
  measurable_denominator n :=
    (left.measurable_denominator n).mul (right.measurable_denominator n)
  approximates s := by
    have hr := right.approximates s
    rw [hworld.posterior_eq s] at hr
    filter_upwards [left.approximates s, hr] with x hx hy
    exact hx.add hy

/-- The second observation's refinement retains the first interval certificate. -/
theorem observed_add (L R : Model Ω S) (hworld : L.SameWorld R)
    (left : Representation L) (right : Representation R) {s t : S} (hst : L.refines s t)
    {n : ℕ} {I J : RationalInterval} (hI : left.Observed s n I) (hJ : right.Observed t n J) :
    (add L R hworld left right).Observed t n (I.add J) := by
  have hJ' : ∀ᵐ x ∂L.posterior t, J = right.interval n x := by
    simpa only [Observed, hworld.posterior_eq t] using hJ
  filter_upwards [left.observed_refines hst hI, hJ'] with x hx hy
  exact congrArg₂ RationalInterval.add hx hy

end Representation

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- Constant reads retain the shared state and return their exact represented interval. -/
theorem represented_point_viewSpec (E : CoPset) (D : Model Ω S) (P : S → IProp GF)
    (c : ℝ) (a b : ℤ) (hb : 0 < b) (hc : c = (a : ℝ) / b) :
    IsRepresentedViewSpec E (D.constant c) (Representation.point D c a b hb hc)
      P (LatentRational.value a b) where
  observe v s n F _ := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨%hv, Hstate⟩
    subst v
    unfold LatentRational.value
    twp_pures
    twp_value
    imodintro
    iexists s, RationalInterval.point a b hb
    iframe Hcredit
    isplitl []
    · ipureintro
      refine ⟨rfl, D.refines_refl s, ?_, Filter.Eventually.of_forall (fun _ => rfl)⟩
      simpa only [hc] using D.encloses_constant s n a b hb
    isimp only [ViewOwns]
    iframe Hstate

theorem represented_constant_viewSpec (E : CoPset) (D : Model Ω S) (P : S → IProp GF)
    (a b : ℤ) (hb : 0 < b) :
    IsRepresentedViewSpec E (D.constant ((a : ℝ) / b)) (Representation.constant D a b hb)
      P (LatentRational.value a b) := represented_point_viewSpec E D P _ a b hb rfl

/-- Addition preserves the actual deterministic intervals and one whole-world credit. -/
theorem represented_add_oracleSpec (E : CoPset) (L R : Model Ω S)
    (hworld : L.SameWorld R) (left : Representation L) (right : Representation R)
    (P : S → IProp GF) (a b : Val rT)
    (ha : IsRepresentedViewSpec E L left P a) (hb : IsRepresentedViewSpec E R right P b) :
    IsRepresentedViewSpec E (L.add R hworld) (Representation.add L R hworld left right)
      P (addVal a b) where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨%hv, Hstate⟩
    subst v
    twp_pures
    twp_bind pl(&a.fst #int (n : ℤ))
    isimp only [Model.add] at Hcredit
    iapply (IsRepresentedViewSpec.wp ha s n F hF _) $$ Hstate Hcredit
    iintro %t %I %hI Hstate Hcredit
    twp_pures
    twp_bind pl(&b.fst #int (n : ℤ))
    isimp only [← hworld.posterior_eq t] at Hcredit
    iapply (IsRepresentedViewSpec.wp hb t n F hF _) $$ Hstate Hcredit
    iintro %u %J %hJ Hstate Hcredit
    twp_pures
    twp_value
    imodintro
    have htu := (hworld.refines_iff t u).mp hJ.1
    iexists u, I.add J
    isplitl []
    · ipureintro
      refine ⟨?_, L.refines_trans hI.1 htu,
        L.encloses_add R hworld (L.encloses_refines htu hI.2.1) hJ.2.1,
        Representation.observed_add L R hworld left right htu hI.2.2 hJ.2.2⟩
      apply Val.ext
      simp [intervalVal, RationalInterval.add, Exp.ofVal]
    isplitl [Hstate]
    · isimp only [ViewOwns]
      iframe Hstate
    isimp only [hworld.posterior_eq u] at Hcredit
    isimp only [Model.add]
    iframe Hcredit

end specification

end

end SampLib.LatentReal
