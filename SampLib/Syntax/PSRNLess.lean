import SampLib.BetaStep
import Samplers.PSRN.Core

/-! # Source correspondence and certified openings for shared-oracle comparison -/

open ProbLang

namespace SampLib.LatentReal.Less.Program

/-- One precision is read from both handles before testing the cross products. -/
def loopCode {rT : Type} (left right : Exp rT) : Exp rT :=
  let bind (rhs body : Exp rT) := .app (.lam body) rhs
  let strict := .binop .lt
    (.binop .mult (.fst (.bvar 1)) (.snd (.bvar 0)))
    (.binop .mult (.fst (.bvar 2)) (.snd (.bvar 1)))
  let reverse := .binop .le
    (.binop .mult (.fst (.bvar 0)) (.snd (.bvar 1)))
    (.binop .mult (.fst (.bvar 3)) (.snd (.bvar 0)))
  let retry := .app (.bvar 5) (.binop .plus (.bvar 4) (.lit (.int 1)))
  let branch := .cond strict (.lit (.bool true)) (.cond reverse (.lit (.bool false)) retry)
  let read := bind (.snd (.bvar 1)) (bind (.snd (.bvar 1)) branch)
  let read := bind (.app right (.bvar 1)) read
  .fix (.lam (bind (.app left (.bvar 0)) read))

def loop {rT : Type} (left right : Val rT) : Exp rT := loopCode left.fst right.fst

private def start {rT : Type} : Exp rT := .app (.bvar 0) (.lit (.int 1))

def sourceBody {rT : Type} : Exp rT :=
  .lam (.app (.lam start) (loopCode (.bvar 3) (.bvar 3)))

def sourceCode {rT : Type} : Exp rT := .lam sourceBody

theorem source_eq {rT : Type} : (Occil.PSRN.less : Exp rT) = sourceCode := by
  kernel_rfl

theorem source_lc {rT : Type} : (sourceCode : Exp rT).IsLocallyClosed := by
  rw [← source_eq]
  is_lc

theorem less_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.PSRN.less = Occil.PSRN.less :=
  (Exp.open_lc k e _ source_lc).symm

def rightBody {rT : Type} (left : Val rT) : Exp rT :=
  .app (.lam start) (loopCode left.fst (.bvar 3))

theorem open_left {rT : Type} (left : Val rT) :
    Exp.open' sourceBody left.fst = .lam (rightBody left) := by
  simp [sourceBody, rightBody, loopCode, start, Exp.open', Exp.openRec]

theorem right_lc {rT : Type} (left : Val rT) :
    (Exp.lam (rightBody left)).IsLocallyClosed := by
  rw [← open_left]
  apply Exp.lcb_imp_lc
  apply Exp.lcb_openRec (Exp.lc_imp_lcb left.lc)
  change Exp.lcb 0 (sourceCode : Exp rT) = true
  exact Exp.lc_imp_lcb source_lc

theorem open_right {rT : Type} [ProbLangℝ rT] (left right : Val rT) :
    Exp.open' (rightBody left) right.fst = pl(let refine := &(loop left right); refine #1) := by
  simp [rightBody, loop, loopCode, start, Exp.open', Exp.openRec,
    (Exp.open_lc 2 right.fst left.fst left.lc).symm]

theorem loop_lc {rT : Type} (left right : Val rT) : (loop left right).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  have hl (k : ℕ) : Exp.lcb k left.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb left.lc) (Nat.zero_le k)
  have hr (k : ℕ) : Exp.lcb k right.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb right.lc) (Nat.zero_le k)
  simp [loop, loopCode, Exp.lcb, hl, hr]

def acceptBody {rT : Type} (right : Val rT) : Exp rT :=
  .app (.app Occil.PSRN.less (.bvar 0)) right.fst

theorem accept_lc {rT : Type} (right : Val rT) :
    (Exp.lam (acceptBody right)).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  have hl (k : ℕ) : Exp.lcb k (Occil.PSRN.less : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb source_lc) (Nat.zero_le k)
  have hr (k : ℕ) : Exp.lcb k right.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb right.lc) (Nat.zero_le k)
  simp [acceptBody, Exp.lcb, hl, hr]

/-- A unary event callback comparing its source handle with the supplied right view. -/
def acceptValue {rT : Type} (right : Val rT) : Val rT :=
  ⟨.lam (acceptBody right), .lam (accept_lc right), accept_lc right⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

/-- Open the fixed handles and retain the named recursive comparison loop. -/
theorem twp_open (E : CoPset) (left right : Val rT) (Φ : Val rT → IProp GF) :
    tglWp E pl(&(loop left right) #1) Φ ⊢
      tglWp E pl(&Occil.PSRN.less &left.fst &right.fst) Φ := by
  iintro H
  rw [source_eq]
  ieval (
    change _ ⊢ tglWp E (Ectx.fill [.appL right]
      (.app (.lam sourceBody) left.fst)) Φ)
  iapply (twp_beta E [.appL right] sourceBody left source_lc Φ)
  rw [open_left]
  ieval (change _ ⊢ tglWp E (Ectx.fill [] (.app (.lam (rightBody left)) right.fst)) Φ)
  iapply (twp_beta E [] (rightBody left) right (right_lc left) Φ)
  rw [open_right]
  let code : Val rT := ⟨loop left right, .fix (loop_lc left right), loop_lc left right⟩
  ieval (
    change _ ⊢ tglWp E (Ectx.fill [] (.app (.lam pl(⟪bvar 0⟫ #1)) code.fst)) Φ)
  iapply (twp_beta E [] pl(⟪bvar 0⟫ #1) code (by is_lc) Φ)
  simp only [Ectx.fill_nil, Exp.open', Exp.openRec, code, ↓reduceIte]
  iexact H

/-- Applying the event callback is exactly the original binary comparison. -/
theorem twp_open_accept (E : CoPset) (left right : Val rT) (Φ : Val rT → IProp GF) :
    tglWp E pl(&Occil.PSRN.less &left.fst &right.fst) Φ ⊢
      tglWp E pl(&(acceptValue right).fst &left.fst) Φ := by
  iintro H
  ieval (
    change _ ⊢ tglWp E (Ectx.fill [] (.app (.lam (acceptBody right)) left.fst)) Φ)
  iapply (twp_beta E [] (acceptBody right) left (accept_lc right) Φ)
  simp only [Ectx.fill_nil, acceptBody, Exp.open', Exp.openRec, less_openRec,
    (Exp.open_lc 0 left.fst right.fst right.lc).symm, ↓reduceIte]
  iexact H

end specification

end SampLib.LatentReal.Less.Program
