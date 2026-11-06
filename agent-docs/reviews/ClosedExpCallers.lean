import SampLib.Core.Syntax.ClosedExp
import Samplers.Uniform

open ProbLang SampLib

namespace ReviewClosedExp

private instance {rT : Type _} : ClosedExp (Occil.uniformInt : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.uniformInt, Exp.fv]

example {rT : Type _} (j k : ℕ) (x : Var) (v : Exp rT) :
    Exp.openRec j v (Exp.closeRec k x Occil.uniformInt) = Occil.uniformInt := by
  simp only [ClosedExp.closeRec, ClosedExp.openRec]

example {rT : Type _} (x : Var) : (Exp.lam (.fvar x) : Exp rT).IsLocallyClosed := by
  is_lc

example {rT : Type _} (x : Var) : ¬ClosedExp (Exp.lam (.fvar x) : Exp rT) := by
  intro h
  have hf := h.fv
  simp [Exp.fv] at hf

#print axioms ClosedExp.openRec
#print axioms ClosedExp.closeRec

end ReviewClosedExp
