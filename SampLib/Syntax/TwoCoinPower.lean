import SampLib.Samplers.RationalCoin
import Samplers.Bernoulli.Powers

/-! # Checked source template for the two-coin power factory -/

open ProbLang

namespace SampLib.TwoCoinPower.Program

def loopCode {rT : Type} (base exponent : Exp rT) : Exp rT :=
  let next := Exp.app (.bvar 1) (.binop .plus (.bvar 0) (.lit (.int 1)))
  .fix (.lam (.cond (.app base (.lit .unit)) (.lit (.bool true))
    (.cond (.app exponent (.lit .unit))
      (.cond (.app (.app Occil.rationalCoin (.lit (.int 1))) (.bvar 0))
        (.lit (.bool false)) next) next)))

@[pl_fold] def loop {rT : Type} (base exponent : Val rT) : Exp rT :=
  loopCode base.fst exponent.fst

def sourceCode {rT : Type} : Exp rT :=
  let next := Exp.app (.bvar 1) (.binop .plus (.bvar 0) (.lit (.int 1)))
  let body := Exp.cond (.app (.bvar 4) (.lit .unit)) (.lit (.bool true))
    (.cond (.app (.bvar 3) (.lit .unit))
      (.cond (.app (.app Occil.rationalCoin (.lit (.int 1))) (.bvar 0))
        (.lit (.bool false)) next) next)
  .lam (.lam (.lam (.app (.lam (.app (.bvar 0) (.lit (.int 1)))) (.fix (.lam body)))))

theorem source_eq {rT : Type} :
    (Occil.FactoryExtra.twoCoinPower : Exp rT) = sourceCode := by kernel_rfl

def source {rT : Type} : Val rT := ⟨sourceCode, .lam (by is_lc), by is_lc⟩

theorem source_fst {rT : Type} :
    (source : Val rT).fst = Occil.FactoryExtra.twoCoinPower := source_eq.symm

end SampLib.TwoCoinPower.Program
