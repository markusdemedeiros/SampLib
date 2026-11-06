import SampLib.PSRN.Support.LatentRepresentedSpec
import SampLib.Core.BetaStep
import Samplers.PSRN.Arithmetic

/-! # Source certificates for the reciprocal refinement loop -/

open ProbLang

namespace SampLib.LatentReal.RepresentedReciprocal.Program

private abbrev bind {rT : Type} (e body : Exp rT) : Exp rT := .app (.lam body) e

def loopCode {rT : Type} (source : Exp rT) : Exp rT :=
  let zero := Exp.binop .and (.binop .eq (.bvar 2) (.lit (.int 0)))
    (.binop .eq (.bvar 1) (.lit (.int 0)))
  let straddle := Exp.binop .and (.binop .le (.bvar 2) (.lit (.int 0)))
    (.binop .le (.lit (.int 0)) (.bvar 1))
  let retry := Exp.app (.bvar 6) (.binop .plus (.bvar 5) (.lit (.int 1)))
  let result := Exp.pair (.binop .mult (.bvar 0) (.bvar 2))
    (.pair (.binop .mult (.bvar 0) (.bvar 1)) (.binop .mult (.bvar 2) (.bvar 1)))
  let branch := Exp.cond zero .fail (.cond straddle retry result)
  let body := bind (.snd (.bvar 2)) branch
  let body := bind (.fst (.bvar 1)) body
  let body := bind (.fst (.bvar 1)) body
  let body := bind (.snd (.bvar 0)) body
  .fix (.lam (bind (.app source (.bvar 0)) body))

@[pl_fold] def loop {rT : Type} (source : Val rT) : Exp rT := loopCode source.fst

private def start {rT : Type} : Exp rT := .app (.bvar 0) (.bvar 1)

def sourceBody {rT : Type} : Exp rT := .lam (bind (loopCode (.bvar 3)) start)

def sourceCode {rT : Type} : Exp rT := .lam sourceBody

theorem source_eq {rT : Type} : (Occil.PSRN.reciprocal : Exp rT) = sourceCode := by
  kernel_rfl

theorem source_lc {rT : Type} : (sourceCode : Exp rT).IsLocallyClosed := by
  rw [← source_eq]
  is_lc

def valueBody {rT : Type} (source : Val rT) : Exp rT := bind (loop source) start

theorem open_source {rT : Type} (source : Val rT) :
    Exp.open' sourceBody source.fst = .lam (valueBody source) := by
  simp [sourceBody, valueBody, loop, loopCode, bind, start, Exp.open', Exp.openRec]

private theorem value_lc {rT : Type} (source : Val rT) :
    (Exp.lam (valueBody source)).IsLocallyClosed := by
  rw [← open_source]
  apply Exp.lcb_imp_lc
  apply Exp.lcb_openRec (Exp.lc_imp_lcb source.lc)
  change Exp.lcb 0 (sourceCode : Exp rT) = true
  exact Exp.lc_imp_lcb source_lc

def value {rT : Type} (source : Val rT) : Val rT :=
  ⟨.lam (valueBody source), .lam (value_lc source), value_lc source⟩

theorem loop_lc {rT : Type} (source : Val rT) : (loop source).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  have hs (k : ℕ) : Exp.lcb k source.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb source.lc) (Nat.zero_le k)
  simp [loop, loopCode, bind, Exp.lcb, hs]

theorem zero_guard_false {rT : Type} [BEq rT] (a : RationalInterval)
    (h : ¬ (a.lower = 0 ∧ a.upper = 0)) :
    (((BaseLit.int a.lower : BaseLit rT) == .int 0) &&
      ((BaseLit.int a.upper : BaseLit rT) == .int 0)) = false := by
  change ((a.lower == 0) && (a.upper == 0)) = false
  by_cases hl : a.lower = 0 <;> by_cases hu : a.upper = 0 <;> simp_all

theorem straddle_false (a : RationalInterval) (h : 0 < a.lower ∨ a.upper < 0) :
    (decide (a.lower ≤ 0) && decide (0 ≤ a.upper)) = false := by
  simpa only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le] using h

theorem straddle_true (a : RationalInterval) (h : ¬ (0 < a.lower ∨ a.upper < 0)) :
    (decide (a.lower ≤ 0) && decide (0 ≤ a.upper)) = true := by
  simpa only [Bool.and_eq_true, decide_eq_true_eq, not_or, not_lt] using h

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

theorem twp_constructor (E : CoPset) (source : Val rT) (Φ : Val rT → IProp GF) :
    Φ (value source) ⊢ tglWp E pl(&Occil.PSRN.reciprocal &source.fst) Φ := by
  iintro H
  rw [source_eq]
  ieval (change _ ⊢ tglWp E (Ectx.fill [] (.app (.lam sourceBody) source.fst)) Φ)
  iapply (twp_beta E [] sourceBody source source_lc Φ)
  rw [open_source]
  simp only [Ectx.fill_nil]
  ieval (change _ ⊢ tglWp E (Exp.ofVal (value source)) Φ)
  iapply (tglWp_value (v := value source))
  iexact H

/-- Expose only the named refinement loop in the public observation proof. -/
theorem twp_open (E : CoPset) (source : Val rT) (n : ℕ) (Φ : Val rT → IProp GF) :
    tglWp E pl(&(loop source) #int (n : ℤ)) Φ ⊢
      tglWp E pl(&(value source).fst #int (n : ℤ)) Φ := by
  iintro H
  ieval (change _ ⊢ tglWp E (Ectx.fill []
    (.app (.lam (valueBody source)) (Val.int (n : ℤ)).fst)) Φ)
  iapply (twp_beta E [] (valueBody source) (Val.int (n : ℤ)) (value_lc source) Φ)
  simp only [valueBody, bind, start, Exp.open', Exp.openRec,
    (Exp.open_lc 0 (Val.int (n : ℤ)).fst (loop source) (loop_lc source)).symm, ↓reduceIte]
  let code : Val rT := ⟨loop source, .fix (loop_lc source), loop_lc source⟩
  ieval (change _ ⊢ tglWp E (Ectx.fill []
    (.app (.lam (.app (.bvar 0) (Val.int (n : ℤ)).fst)) code.fst)) Φ)
  iapply (twp_beta E [] (.app (.bvar 0) (Val.int (n : ℤ)).fst) code (by is_lc) Φ)
  simp only [Ectx.fill_nil, Exp.open', Exp.openRec, code, ↓reduceIte]
  iexact H

end specification

end SampLib.LatentReal.RepresentedReciprocal.Program
