import SampLib.LatentViews
import SampLib.BetaStep
import SampLib.IntMinMax
import SampLib.Syntax.ClosedExp
import SampLib.Distributions.LatentReal.IntervalProductError
import Samplers.PSRN.Arithmetic

/-! # Multiplying two views of one shared latent world

The error estimate is pointwise in both latent values. Reading the two handles
threads one physical ownership, even when the handles or their operands alias.
-/

open ProbLang
open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

namespace Model

variable {Ω S : Type} [MeasurableSpace Ω]

/-- The product error consists of two linear perturbations and their cross term. -/
def multiply (left right : Model Ω S) (h : SameWorld left right) : Model Ω S :=
  { left with
    value := fun x => left.value x * right.value x
    measurable_value := left.measurable_value.mul right.measurable_value
    error := fun n x => 2 * (left.error n x * |right.value x| +
      |left.value x| * right.error n x + left.error n x * right.error n x)
    error_tendsto := fun s => by
      have hr := right.error_tendsto s
      rw [h.posterior_eq s] at hr
      filter_upwards [left.error_tendsto s, hr] with x hx hy
      simpa only [zero_mul, mul_zero, add_zero] using
        ((hx.mul_const |right.value x|).add (hy.const_mul |left.value x|)).add
          (hx.mul hy) |>.const_mul 2 }

/-- Four-corner multiplication encloses the product under the common final posterior. -/
theorem encloses_multiply (left right : Model Ω S) (h : SameWorld left right)
    {s : S} {n : ℕ} {I J : RationalInterval}
    (hI : left.Encloses s n I) (hJ : right.Encloses s n J) :
    (left.multiply right h).Encloses s n (I.multiply J) := by
  have hJ' : ∀ᵐ x ∂left.posterior s,
      J.Contains (right.value x) ∧ J.width ≤ right.error n x := by
    simpa only [Encloses, RationalInterval.width, h.posterior_eq s] using hJ
  filter_upwards [hI, hJ'] with x hx hy
  exact ⟨I.contains_multiply J hx.1 hy.1, I.width_multiply_le J hx.1 hy.1 hx.2 hy.2⟩

end Model

private def multiplyCode {rT : Type} (left right : Exp rT) : Exp rT :=
  let bind (e body : Exp rT) : Exp rT := .app (.lam body) e
  let minimum : Exp rT :=
    .lam (.lam (.cond (.binop .lt (.bvar 1) (.bvar 0)) (.bvar 1) (.bvar 0)))
  let maximum : Exp rT :=
    .lam (.lam (.cond (.binop .lt (.bvar 1) (.bvar 0)) (.bvar 0) (.bvar 1)))
  let apply₂ (f x y : Exp rT) := .app (.app f x) y
  let result : Exp rT := .pair
    (apply₂ (.bvar 5) (apply₂ (.bvar 5) (.bvar 3) (.bvar 2))
      (apply₂ (.bvar 5) (.bvar 1) (.bvar 0)))
    (.pair
      (apply₂ (.bvar 4) (apply₂ (.bvar 4) (.bvar 3) (.bvar 2))
        (apply₂ (.bvar 4) (.bvar 1) (.bvar 0)))
      (.binop .mult (.snd (.bvar 7)) (.snd (.bvar 6))))
  let bb := bind (.binop .mult (.fst (.bvar 6)) (.fst (.bvar 5))) result
  let ba := bind (.binop .mult (.fst (.bvar 5)) (.fst (.bvar 6))) bb
  let ab := bind (.binop .mult (.fst (.bvar 6)) (.fst (.bvar 3))) ba
  let aa := bind (.binop .mult (.fst (.bvar 5)) (.fst (.bvar 4))) ab
  let ranges := bind (.snd (.bvar 1))
    (bind (.snd (.bvar 1)) (bind minimum (bind maximum aa)))
  let readRight := bind (.app right (.bvar 1)) ranges
  .lam (bind (.app left (.bvar 0)) readRight)

/-- The actual multiplication closure, with handles inserted after closing binders. -/
def multiplyVal {rT : Type} (left right : Val rT) : Val rT :=
  ⟨multiplyCode left.fst right.fst, .lam (by
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
    simp [multiplyCode, Exp.lcb, hl, hr]⟩

private def multiplyBody {rT : Type} : Exp rT :=
  match (Occil.PSRN.multiply : Exp rT) with
  | .lam (.lam body) => body
  | _ => .lit .unit

private theorem multiplyBody_lcb {rT : Type} :
    Exp.lcb 2 (multiplyBody (rT := rT)) = true := by lcb_decide

private def source {rT : Type} : Val rT := by
  have hc : (Exp.lam (.lam (multiplyBody (rT := rT)))).IsLocallyClosed :=
    Exp.lcb_imp_lc (show Exp.lcb 0 (.lam (.lam (multiplyBody (rT := rT)))) = true from
      multiplyBody_lcb (rT := rT))
  exact ⟨.lam (.lam multiplyBody), .lam hc, hc⟩

private theorem source_fst {rT : Type} : (source (rT := rT)).fst = Occil.PSRN.multiply := rfl

private def partialSource {rT : Type} (left : Val rT) : Val rT := by
  have hc : (Exp.lam (Exp.openRec 1 left.fst (multiplyBody (rT := rT)))).IsLocallyClosed :=
    Exp.lcb_imp_lc (show Exp.lcb 1 (Exp.openRec 1 left.fst multiplyBody) = true from
      Exp.lcb_openRec (Exp.lcb_ofVal 1 left) (multiplyBody_lcb (rT := rT)))
  exact ⟨.lam (Exp.openRec 1 left.fst multiplyBody), .lam hc, hc⟩

private theorem opened_source {rT : Type} (left right : Val rT) :
    Exp.open' (Exp.openRec 1 left.fst multiplyBody) right.fst =
      multiplyCode left.fst right.fst := by
  simp [multiplyBody, Occil.PSRN.multiply, Exp.open', Exp.openRec, Exp.close, Exp.closeRec,
    Var.internal.injEq, ProbLang.openRec_val_fst, multiplyCode]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

private theorem source_beta (E : CoPset) (left right : Val rT) (Φ : Val rT → IProp GF) :
    tglWp E pl(&(partialSource left).fst &right.fst) Φ ⊢
      tglWp E pl(&(source (rT := rT)).fst &left.fst &right.fst) Φ :=
  twp_beta E [.appL right] (.lam multiplyBody) left (source (rT := rT)).lc Φ

private theorem left_beta (E : CoPset) (left right : Val rT) (Φ : Val rT → IProp GF) :
    tglWp E (Exp.open' (Exp.openRec 1 left.fst multiplyBody) right.fst) Φ ⊢
      tglWp E pl(&(partialSource left).fst &right.fst) Φ :=
  twp_beta E [] (Exp.openRec 1 left.fst multiplyBody) right (partialSource left).lc Φ

private theorem value_step (E : CoPset) (left right : Val rT) (Φ : Val rT → IProp GF) :
    Φ (multiplyVal left right) ⊢ tglWp E (multiplyCode left.fst right.fst) Φ :=
  tglWp_value (E := E) (v := multiplyVal left right)

/-- Capturing the handles does not observe either operand. -/
theorem twp_multiply (E : CoPset) (left right : Val rT) (P : S → IProp GF) (s : S) :
    iprop(P s) ⊢ tglWp E pl(&Occil.PSRN.multiply &left.fst &right.fst)
      (fun v => ViewOwns (multiplyVal left right) P v s) := by
  iintro Hstate
  rw [← source_fst]
  iapply source_beta E left right _
  iapply left_beta E left right _
  rw [opened_source]
  iapply value_step E left right _
  isimp only [ViewOwns]
  iframe Hstate

/-- Every product read retains one common posterior and its physical state. -/
theorem multiply_oracleSpec (E : CoPset) (Dleft Dright : Model Ω S)
    (hworld : Dleft.SameWorld Dright) (P : S → IProp GF) (left right : Val rT)
    (hleft : IsViewSpec E Dleft P left) (hright : IsViewSpec E Dright P right) :
    IsOracleSpec E (Dleft.multiply Dright hworld) (ViewOwns (multiplyVal left right) P) where
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
    have hI' := Dleft.encloses_refines htu hI.2
    iexists u, I.multiply J
    isplit
    · ipureintro
      refine ⟨?_, Dleft.refines_trans hI.1 htu,
        Dleft.encloses_multiply Dright hworld hI' hJ.2⟩
      apply Val.ext
      simp [intervalVal, RationalInterval.multiply, Exp.ofVal, min_def, max_def]
    isplitl [Hstate]
    · isimp only [ViewOwns]
      iframe Hstate
    isimp only [hworld.posterior_eq u] at Hcredit
    isimp only [Model.multiply]
    iframe Hcredit

end specification

end

end SampLib.LatentReal
