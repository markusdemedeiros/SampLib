import Metrology.ProbLang.Syntax.LocallyClosed

/-! # Closed constants under object-language binders

Local instances let sampler proofs normalize known constants with two fixed
rewrite rules. No instance is provided for arbitrary locally closed values:
their free variables must be preserved when constructing callbacks.
-/

open ProbLang

namespace SampLib

/-- A source expression with neither unbound indices nor free variables. -/
class ClosedExp {rT : Type _} (e : Exp rT) : Prop where
  lc : e.IsLocallyClosed
  fv : e.fv = ∅

namespace ClosedExp

theorem openRec {rT : Type _} {e : Exp rT} [ClosedExp e] (k : ℕ) (v : Exp rT) :
    Exp.openRec k v e = e := (Exp.open_lc k v e ClosedExp.lc).symm

theorem closeRec {rT : Type _} {e : Exp rT} [ClosedExp e] (k : ℕ) (x : Var) :
    Exp.closeRec k x e = e := Exp.closeRec_fresh x e k (by simp [ClosedExp.fv])

end ClosedExp

end SampLib
