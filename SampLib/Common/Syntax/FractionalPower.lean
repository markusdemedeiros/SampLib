import SampLib.Uniform.RationalCoin
import Samplers.Bernoulli.Basic

/-! # Checked source template for the fractional-power factory

The source equality is checked before inserting arbitrary locally closed callbacks.
The lambda body is structural, so pure steps need no stronger callback closure premise.
-/

open ProbLang

namespace SampLib.FractionalPower.Program

def loopCode {rT : Type} (coin a b : Exp rT) : Exp rT :=
  .fix (.lam (.cond (.app coin (.lit .unit)) (.lit (.bool true))
    (.cond (.app (.app Occil.rationalCoin a) (.binop .mult b (.bvar 0)))
      (.lit (.bool false)) (.app (.bvar 1) (.binop .plus (.bvar 0) (.lit (.int 1)))))))

@[pl_fold] def loop {rT : Type} (coin : Val rT) (a b : ℤ) : Exp rT :=
  loopCode coin.fst (.lit (.int a)) (.lit (.int b))

def sourceCode {rT : Type} : Exp rT :=
  let guard := Exp.binop .or (.binop .le (.bvar 2) (.lit (.int 0)))
    (.binop .lt (.bvar 1) (.bvar 2))
  let body := Exp.cond (.app (.bvar 5) (.lit .unit)) (.lit (.bool true))
    (.cond (.app (.app Occil.rationalCoin (.bvar 4))
      (.binop .mult (.bvar 3) (.bvar 0))) (.lit (.bool false))
      (.app (.bvar 1) (.binop .plus (.bvar 0) (.lit (.int 1)))))
  let start := Exp.app (.lam (.app (.bvar 0) (.lit (.int 1)))) (.fix (.lam body))
  .lam (.lam (.lam (.lam (.cond guard .fail start))))

theorem source_eq {rT : Type} :
    (Occil.fractionalPower : Exp rT) = sourceCode := by kernel_rfl

def source {rT : Type} : Val rT :=
  ⟨sourceCode, .lam (by is_lc), by is_lc⟩

theorem source_fst {rT : Type} :
    (source : Val rT).fst = Occil.fractionalPower := source_eq.symm

theorem fractionalPower_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.fractionalPower = Occil.fractionalPower :=
  (Exp.open_lc k e _ (by is_lc)).symm

theorem fractionalPower_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.fractionalPower : Exp rT) = Occil.fractionalPower := by
  apply Exp.closeRec_fresh
  simp [source_eq, sourceCode, Exp.fv, RationalCoin.rationalCoin_fv]

end SampLib.FractionalPower.Program
