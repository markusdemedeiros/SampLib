import SampLib.Core.Syntax.ClosedExp
import Samplers.PSRN.Uniform

/-! # Closed source syntax for the deferred uniform-sum proof -/

open ProbLang

namespace SampLib.PSRNUniformSum

scoped instance rational_closed {rT : Type} : ClosedExp (Occil.PSRN.rational : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.PSRN.rational, Exp.fv]

scoped instance add_closed {rT : Type} : ClosedExp (Occil.PSRN.add : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.PSRN.add, Exp.fv]

scoped instance uniform_closed {rT : Type} : ClosedExp (Occil.PSRN.newUniform : Exp rT) where
  lc := by is_lc
  fv := by
    simp [Occil.PSRN.newUniform, Occil.PSRN.fromUniformBag, Occil.PSRN.integerPower,
      Occil.uniformBagPrefix, Occil.uniformBagStep, Occil.newUniformBag,
      Occil.fairCoin, Exp.fv]

scoped instance sum_closed {rT : Type} : ClosedExp (Occil.PSRN.newUniformSum : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.PSRN.newUniformSum, Exp.fv, ClosedExp.closeRec, ClosedExp.fv]

def sumCode {rT : Type} : Exp rT :=
  .fix (.lam (.cond (.binop .lt (.bvar 0) (.lit (.int 0))) .fail
    (.cond (.binop .eq (.bvar 0) (.lit (.int 0)))
      (.app (.app Occil.PSRN.rational (.lit (.int 0))) (.lit (.int 1)))
      (.app (.lam (.app (.app Occil.PSRN.add (.bvar 0))
        (.app (.bvar 2) (.binop .minus (.bvar 1) (.lit (.int 1))))))
        (.app Occil.PSRN.newUniform (.lit .unit))))))

theorem source_eq_code {rT : Type} :
    (Occil.PSRN.newUniformSum : Exp rT) = sumCode := by
  simp [Occil.PSRN.newUniformSum, sumCode, Exp.close, Exp.closeRec,
    ClosedExp.closeRec, Var.internal.injEq]

end SampLib.PSRNUniformSum
