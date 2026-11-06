import SampLib.Core.CurriedStep
import SampLib.Core.Syntax.ClosedExp
import Samplers.PSRN.BetaGamma

/-! # The subunit-shape branch of the actual beta constructor

The source tests its guards in order. With both shapes in `(0,1)` it reaches
Johnk's retry loop, kept here as a named closed expression.
-/

open ProbLang

namespace SampLib.PSRNJohnkBeta.Program

scoped instance power_closed {rT : Type} : ClosedExp (Occil.PSRN.newPowerUniform : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

scoped instance add_closed {rT : Type} : ClosedExp (Occil.PSRN.add : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

scoped instance less_closed {rT : Type} : ClosedExp (Occil.PSRN.less : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

scoped instance rational_closed {rT : Type} : ClosedExp (Occil.PSRN.rational : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

scoped instance divide_closed {rT : Type} : ClosedExp (Occil.PSRN.divide : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

open scoped SampLib.PSRNJohnkBeta.Program

/-- Johnk's loop: two power proposals, accepted when their sum is below one. -/
def loop {rT : Type} (an ad bn bd : ℤ) : Exp rT :=
  .fix (.lam
    (.app (.lam
      (.app (.lam
        (.app (.lam
          (.cond
            (.app (.app Occil.PSRN.less (.bvar 0))
              (.app (.app Occil.PSRN.rational (.lit (.int 1))) (.lit (.int 1))))
            (.app (.app Occil.PSRN.divide (.bvar 2)) (.bvar 0))
            (.app (.bvar 4) (.lit .unit))))
          (.app (.app Occil.PSRN.add (.bvar 1)) (.bvar 0))))
        (.app (.app (.app Occil.PSRN.newPowerUniform (.lit (.int bd))) (.lit (.int bn)))
          (.lit .unit))))
      (.app (.app (.app Occil.PSRN.newPowerUniform (.lit (.int ad))) (.lit (.int an)))
        (.lit .unit))))

/-- The source's call constructing one power proposal. -/
def proposal {rT : Type} (d n : ℤ) : Exp rT :=
  .app (.app (.app Occil.PSRN.newPowerUniform (.lit (.int d))) (.lit (.int n))) (.lit .unit)

theorem proposal_eq {rT : Type} (d n : ℤ) :
    (pl(&Occil.PSRN.newPowerUniform #d #n #()) : Exp rT) = proposal d n := by
  rfl

/-- The loop before the four shape parameters are substituted. -/
private def loopCode {rT : Type} : Exp rT :=
  .fix (.lam
    (.app (.lam
      (.app (.lam
        (.app (.lam
          (.cond
            (.app (.app Occil.PSRN.less (.bvar 0))
              (.app (.app Occil.PSRN.rational (.lit (.int 1))) (.lit (.int 1))))
            (.app (.app Occil.PSRN.divide (.bvar 2)) (.bvar 0))
            (.app (.bvar 4) (.lit .unit))))
          (.app (.app Occil.PSRN.add (.bvar 1)) (.bvar 0))))
        (.app (.app (.app Occil.PSRN.newPowerUniform (.bvar 4)) (.bvar 5)) (.lit .unit))))
      (.app (.app (.app Occil.PSRN.newPowerUniform (.bvar 5)) (.bvar 6)) (.lit .unit))))

private def body {rT : Type} : Exp rT :=
  match (Occil.PSRN.newBeta : Exp rT) with
  | .lam (.lam (.lam (.lam (.lam e)))) => e
  | _ => .fail

private def branch {rT : Type} : ℕ → Exp rT → Exp rT
  | 0, .cond _ e _ => e
  | k + 1, .cond _ _ e => branch k e
  | _, _ => .fail

private def rest {rT : Type} : ℕ → Exp rT → Exp rT
  | 0, .cond _ _ e => e
  | k + 1, .cond _ _ e => rest k e
  | _, _ => .fail

private def le0 {rT : Type} (k : ℕ) : Exp rT := .binop .le (.bvar k) (.lit (.int 0))

private def divisible {rT : Type} (n d : ℕ) : Exp rT :=
  .binop .eq (.binop .mod (.bvar n) (.bvar d)) (.lit (.int 0))

/-- The guards and branch structure of the source, with the Johnk branch exposed. -/
private def code {rT : Type} : Exp rT :=
  .cond (.binop .or (.binop .or (.binop .or (le0 3) (le0 1)) (le0 4)) (le0 2)) .fail
    (.cond (.binop .and (divisible 4 3) (divisible 2 1)) (branch 1 body)
      (.cond (.binop .eq (.bvar 2) (.bvar 1)) (branch 2 body)
        (.cond (.binop .eq (.bvar 4) (.bvar 3)) (branch 3 body)
          (.cond (.binop .and (.binop .le (.bvar 3) (.bvar 4)) (.binop .le (.bvar 1) (.bvar 2)))
            (branch 4 body)
            (.cond (.binop .and (.binop .lt (.bvar 4) (.bvar 3)) (.binop .lt (.bvar 2) (.bvar 1)))
              (.app (.lam (.app (.bvar 0) (.lit .unit))) loopCode)
              (rest 5 body))))))

private theorem opened_loop {rT : Type} (an ad bn bd : ℤ) :
    Exp.openRec 0 (.lit .unit) (Exp.openRec 1 (.lit (.int bd)) (Exp.openRec 2 (.lit (.int bn))
      (Exp.openRec 3 (.lit (.int ad)) (Exp.openRec 4 (.lit (.int an)) loopCode)))) =
      (loop an ad bn bd : Exp rT) := by
  simp [loopCode, loop, Exp.openRec, ClosedExp.openRec]

private theorem source_eq {rT : Type} :
    (Occil.PSRN.newBeta : Exp rT) = CurriedStep.lambdas 5 code := by
  kernel_rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

private theorem int_beq {rT : Type} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

private def args {rT : Type} (an ad bn bd : ℤ) : List (Val rT) :=
  [.int an, .int ad, .int bn, .int bd, .unit]

/-- Subunit shapes pass every earlier guard and enter Johnk's loop. -/
theorem twp_open (E : CoPset) (an ad bn bd : ℤ) (han : 0 < an) (hab : an < ad)
    (hbn : 0 < bn) (hbb : bn < bd) (Φ : Val rT → IProp GF) :
    tglWp E (.app (loop an ad bn bd) (.lit .unit)) Φ ⊢
      tglWp E pl(&Occil.PSRN.newBeta #an #ad #bn #bd #()) Φ := by
  have h := CurriedStep.twp_apply (GF := GF) E [] (args an ad bn bd) code (by kernel_rfl) Φ
  rw [source_eq]
  refine BI.BIBase.Entails.trans ?_ h
  simp only [args, CurriedStep.opened, code, Exp.openRec, le0, divisible, List.length_cons,
    List.length_nil, Ectx.fill, Nat.reduceAdd, Nat.zero_add, ↓reduceIte, Nat.reduceEqDiff,
    List.foldl_nil, opened_loop]
  have hmod : ¬an % ad = 0 := by rw [Int.emod_eq_of_lt han.le hab]; omega
  iintro H
  twp_pures
  rw [show (((decide (ad ≤ 0)).or (decide (bd ≤ 0))).or (decide (an ≤ 0))).or
      (decide (bn ≤ 0)) = false by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_le]; omega]
  twp_pures
  have h1 : (an % ad == 0) = false := by simpa using hmod
  have h2 : (bn == bd) = false := by simp only [beq_eq_false_iff_ne]; omega
  have h3 : (an == ad) = false := by simp only [beq_eq_false_iff_ne]; omega
  have h4 : decide (ad ≤ an) = false := by simp only [decide_eq_false_iff_not]; omega
  have h5 : decide (an < ad) = true := decide_eq_true hab
  have h6 : decide (bn < bd) = true := decide_eq_true hbb
  rw [int_beq, h1, Bool.false_and]
  twp_pures
  rw [int_beq, h2]
  twp_pures
  rw [int_beq, h3]
  twp_pures
  rw [h4, Bool.false_and]
  twp_pures
  rw [h5, h6, Bool.and_self]
  twp_pure
  twp_pure
  iexact H

end specification

end SampLib.PSRNJohnkBeta.Program
