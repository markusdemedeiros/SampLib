import SampLib.LatentViews
import Samplers.PSRN.Arithmetic

/-! # Adding two views of one latent world

The two calls thread one physical ownership predicate. The first enclosure is
transported through the second call's refinement, retaining aliases and correlation.
-/

open ProbLang
open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

namespace Model

variable {Ω S : Type} [MeasurableSpace Ω]

/-- Addition changes the real projection and adds its two error envelopes. -/
def add (left right : Model Ω S) (h : SameWorld left right) : Model Ω S :=
  { left with
    value := fun x => left.value x + right.value x
    measurable_value := left.measurable_value.add right.measurable_value
    error := fun n x => left.error n x + right.error n x
    error_tendsto := fun s => by
      have hr := right.error_tendsto s
      rw [h.posterior_eq s] at hr
      filter_upwards [left.error_tendsto s, hr] with x hx hy
      simpa only [add_zero] using hx.add hy }

/-- Both enclosures refer to the same latent point under the final shared posterior. -/
theorem encloses_add (left right : Model Ω S) (h : SameWorld left right)
    {s : S} {n : ℕ} {I J : RationalInterval}
    (hI : left.Encloses s n I) (hJ : right.Encloses s n J) :
    (left.add right h).Encloses s n (I.add J) := by
  have hJ' : ∀ᵐ x ∂left.posterior s,
      J.Contains (right.value x) ∧ J.width ≤ right.error n x := by
    simpa only [Encloses, RationalInterval.width, h.posterior_eq s] using hJ
  filter_upwards [hI, hJ'] with x hx hy
  refine ⟨I.contains_add J hx.1 hy.1, ?_⟩
  change (I.add J).width ≤ left.error n x + right.error n x
  rw [RationalInterval.width_add]
  exact add_le_add hx.2 hy.2

end Model

private def addCode {rT : Type} (left right : Exp rT) : Exp rT :=
  let result : Exp rT := .pair
    (.binop .plus
      (.binop .mult (.fst (.bvar 3)) (.snd (.bvar 0)))
      (.binop .mult (.fst (.bvar 2)) (.snd (.bvar 1))))
    (.pair
      (.binop .plus
        (.binop .mult (.fst (.bvar 1)) (.snd (.bvar 0)))
        (.binop .mult (.fst (.bvar 0)) (.snd (.bvar 1))))
      (.binop .mult (.snd (.bvar 1)) (.snd (.bvar 0))))
  let ranges := .app (.lam (.app (.lam result) (.snd (.bvar 1)))) (.snd (.bvar 1))
  let readRight := .app (.lam ranges) (.app right (.bvar 1))
  .lam (.app (.lam readRight) (.app left (.bvar 0)))

/-- The actual addition closure, with handles inserted after its binders are closed. -/
def addVal {rT : Type} (left right : Val rT) : Val rT :=
  ⟨addCode left.fst right.fst, .lam (by
    apply Exp.lcb_imp_lc
    have hl (n : ℕ) : Exp.lcb n left.fst = true :=
      Exp.lcb_mono (Exp.lc_imp_lcb left.lc) (Nat.zero_le n)
    have hr (n : ℕ) : Exp.lcb n right.fst = true :=
      Exp.lcb_mono (Exp.lc_imp_lcb right.lc) (Nat.zero_le n)
    simp [Exp.lcb, hl, hr]), by
    apply Exp.lcb_imp_lc
    have hl (n : ℕ) : Exp.lcb n left.fst = true :=
      Exp.lcb_mono (Exp.lc_imp_lcb left.lc) (Nat.zero_le n)
    have hr (n : ℕ) : Exp.lcb n right.fst = true :=
      Exp.lcb_mono (Exp.lc_imp_lcb right.lc) (Nat.zero_le n)
    simp [addCode, Exp.lcb, hl, hr]⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- Constructing the sum merely captures both handles and retains the common state. -/
theorem twp_add (E : CoPset) (left right : Val rT) (P : S → IProp GF) (s : S) :
    iprop(P s) ⊢ tglWp E pl(&Occil.PSRN.add &left.fst &right.fst)
      (fun v => ViewOwns (addVal left right) P v s) := by
  iintro Hstate
  twp_pures
  twp_value
  imodintro
  isimp only [ViewOwns]
  iframe Hstate
  ipureintro
  apply Val.ext
  simp [addVal, addCode]

/-- Sequential observations preserve one shared world, even if the handles alias. -/
theorem add_oracleSpec (E : CoPset) (Dleft Dright : Model Ω S)
    (hworld : Dleft.SameWorld Dright) (P : S → IProp GF) (left right : Val rT)
    (hleft : IsViewSpec E Dleft P left) (hright : IsViewSpec E Dright P right) :
    IsOracleSpec E (Dleft.add Dright hworld) (ViewOwns (addVal left right) P) where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨%hv, Hstate⟩
    subst v
    twp_pures
    twp_bind pl(&left.fst #int (n : ℤ))
    isimp only [Model.add] at Hcredit
    iapply hleft.wp s n F hF _ $$ Hstate Hcredit
    iintro %t %I %hI Hstate Hcredit
    twp_pures
    twp_bind pl(&right.fst #int (n : ℤ))
    isimp only [← hworld.posterior_eq t] at Hcredit
    iapply hright.wp t n F hF _ $$ Hstate Hcredit
    iintro %u %J %hJ Hstate Hcredit
    twp_pures
    twp_value
    imodintro
    have htu := (hworld.refines_iff t u).mp hJ.1
    have hI' := Dleft.encloses_refines htu hI.2
    iexists u, I.add J
    isplit
    · ipureintro
      refine ⟨?_, Dleft.refines_trans hI.1 htu, Dleft.encloses_add Dright hworld hI' hJ.2⟩
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
