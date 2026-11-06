import SampLib.TrigonometricCoefficients
import SampLib.ArcsineCoefficients
import SampLib.UniformBagChoice
import Samplers.Bernoulli.Trigonometric

/-! Pure transport from the source's evaluated local callbacks to their shared binder forms. -/

open ProbLang

namespace SampLib.TrigonometricCallbacks

private instance alternating_closed {rT : Type} :
    ClosedExp (Occil.FactoryExtra.alternatingSeries : Exp rT) where
  lc := by is_lc
  fv := by
    simp [Occil.FactoryExtra.alternatingSeries, Occil.newUniformBag, Exp.fv,
      UniformBag.uniformBagLess_fv, ClosedExp.closeRec, ClosedExp.fv]

private instance choose_closed {rT : Type} : ClosedExp (Occil.FactoryExtra.choose : Exp rT) where
  lc := FactoryChoose.choose_lc
  fv := FactoryChoose.choose_fv

private instance power_closed {rT : Type} : ClosedExp (Occil.FactoryExtra.intPower : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.FactoryExtra.intPower, Exp.fv]

def cosineCall {rT : Type} (coin : Exp rT) : Exp rT := pl(
  &Occil.FactoryExtra.alternatingSeries &coin
    (fun n, (#1, (rec product n := if n <= #1 then #1 else n * product (n - #1)) (#2 * n)))
    #())

def sincCall {rT : Type} (coin : Exp rT) (a b : ℤ) : Exp rT := pl(
  &Occil.FactoryExtra.alternatingSeries &coin
    (fun n, (&Occil.FactoryExtra.intPower #int a n,
      &Occil.FactoryExtra.intPower #int b n *
        (rec product n := if n <= #1 then #1 else n * product (n - #1)) (#2 * n + #1))) #())

def arcsineCall {rT : Type} (coin : Exp rT) : Exp rT := pl(
  &Occil.FactoryExtra.alternatingSeries &coin
    (fun n,
      let degree := n + #1;
      let k := degree / #2;
      let factor := (if degree % #2 = #1 then degree else degree - #1);
      (&Occil.FactoryExtra.choose (#2 * k) k, &Occil.FactoryExtra.intPower #4 k * factor)) #())

theorem cosineCall_eq {rT : Type} (coin : Exp rT) :
    cosineCall coin = .app (.app (.app Occil.FactoryExtra.alternatingSeries coin)
      TrigonometricCoefficients.cosineCode) (.lit .unit) := by
  simp [cosineCall, TrigonometricCoefficients.cosineCode, FactorialCallback.factorialCode,
    Exp.close, Exp.closeRec, Var.internal.injEq]

theorem sincCall_eq {rT : Type} (coin : Exp rT) (a b : ℤ) :
    sincCall coin a b = .app (.app (.app Occil.FactoryExtra.alternatingSeries coin)
      (TrigonometricCoefficients.sincCode a b)) (.lit .unit) := by
  simp [sincCall, TrigonometricCoefficients.sincCode, FactorialCallback.factorialCode,
    Exp.close, Exp.closeRec, Var.internal.injEq, ClosedExp.closeRec]

theorem arcsineCall_eq {rT : Type} (coin : Exp rT) :
    arcsineCall coin = .app (.app (.app Occil.FactoryExtra.alternatingSeries coin)
      ArcsineCoefficients.coefficientCode) (.lit .unit) := by
  simp [arcsineCall, ArcsineCoefficients.coefficientCode, Exp.close, Exp.closeRec,
    Var.internal.injEq, ClosedExp.closeRec]

end SampLib.TrigonometricCallbacks
