import SampLib.Syntax.PSRNRoot
import SampLib.PSRNRootBelow
import SampLib.Syntax.PSRNRootLoops

/-! # Opening one root observation into named arithmetic and search stages -/

open ProbLang

namespace SampLib.LatentReal.Root.Program

private instance less_closed {rT : Type} : ClosedExp (Occil.PSRN.less : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.PSRN.less, Exp.fv]

private instance rational_closed {rT : Type} : ClosedExp (Occil.PSRN.rational : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.PSRN.rational, Exp.fv]

/-- The callback captures the already computed denominator power. -/
def callbackCode {rT : Type} (source : Exp rT) (degree : ℕ) (power : Exp rT) : Exp rT :=
  .lam (.app (.lam (.app (.app Occil.PSRN.less source)
    (.app (.app Occil.PSRN.rational (.bvar 0)) power)))
    (.app (.app Occil.PSRN.integerPower (.bvar 0)) (.lit (.int (degree : ℤ)))))

def searchCode {rT : Type} (below denominator : Exp rT) : Exp rT :=
  let stop := .binop .le (.binop .minus (.bvar 0) (.bvar 1)) (.lit (.int 1))
  let result := .pair (.bvar 1) (.pair (.bvar 0) denominator)
  let lower := .app (.app (.bvar 3) (.bvar 2)) (.bvar 0)
  let upper := .app (.app (.bvar 3) (.bvar 0)) (.bvar 1)
  let mid := .binop .div (.binop .plus (.bvar 1) (.bvar 0)) (.lit (.int 2))
  .fix (.lam (.lam (.cond stop result
    (.app (.lam (.cond (.app below (.bvar 0)) lower upper)) mid))))

/-- The exact post-beta source syntax, with the source inserted after binder construction. -/
def observeCode {rT : Type} (source : Val rT) (degree n : ℕ) : Exp rT :=
  let bind (rhs body : Exp rT) := .app (.lam body) rhs
  let finish := .app (.app (.bvar 0) (.lit (.int 0))) (.bvar 1)
  let search := bind (searchCode (.bvar 6) (.bvar 7)) finish
  let upper := bind (.app (.bvar 0) (.bvar 3)) search
  let bracket := bind (bracketCode (.bvar 2)) upper
  let callback := bind (callbackCode source.fst degree (.bvar 2)) bracket
  let power := bind (.app (.app Occil.PSRN.integerPower (.bvar 0))
    (.lit (.int (degree : ℤ)))) callback
  let denominator := bind (.app (.app Occil.PSRN.integerPower (.lit (.int 2)))
    (.lit (.int (n : ℤ)))) power
  .cond (.binop .lt (.lit (.int (n : ℤ))) (.lit (.int 0))) .fail denominator

/-- The precision binder's body, kept opaque during the beta step. -/
def body {rT : Type} (source : Val rT) (degree : ℕ) : Exp rT :=
  match code source degree with
  | .lam body => body
  | _ => .fail

private theorem open_body {rT : Type} (source : Val rT) (degree n : ℕ) :
    Exp.open' (body source degree) (Val.int (n : ℤ)).fst = observeCode source degree n := by
  have hs (k : ℕ) (e : Exp rT) : Exp.openRec k e source.fst = source.fst :=
    (Exp.open_lc k e source.fst source.lc).symm
  simp [body, code, observerBody, Occil.PSRN.root, observeCode, callbackCode,
    bracketCode, searchCode, Exp.open',
    ClosedExp.openRec, ClosedExp.closeRec, Exp.openRec, Exp.closeRec, hs]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

/-- A single certified beta step exposes one precision request without expanding its loops. -/
theorem twp_open_observe (E : CoPset) (source : Val rT) (degree n : ℕ)
    (Φ : Val rT → IProp GF) :
    tglWp E (observeCode source degree n) Φ ⊢
      tglWp E pl(&(value source degree).fst #int (n : ℤ)) Φ := by
  iintro H
  ieval (
    change _ ⊢ tglWp E (Ectx.fill [] (.app (.lam (body source degree)) (Val.int (n : ℤ)).fst)) Φ)
  have hc : (Exp.lam (body source degree)).IsLocallyClosed := (value source degree).lc
  iapply (twp_beta E [] (body source degree) (Val.int (n : ℤ)) hc Φ)
  rw [open_body]
  simp only [Ectx.fill_nil]
  iexact H

end specification

end SampLib.LatentReal.Root.Program
