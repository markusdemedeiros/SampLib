import Samplers.Combinatorial.Basic
import Metrology.ProbLang.Syntax.LocallyClosed

/-! # Closed list and array routines under sampler binders -/

open ProbLang

namespace SampLib.ArraySyntax

@[simp] theorem length_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.length = Occil.length :=
  (Exp.open_lc k e _ (by is_lc)).symm

@[simp] theorem length_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.length : Exp rT) = Occil.length :=
  Exp.closeRec_fresh x _ k (by simp [Occil.length, Exp.fv])

@[simp] theorem fillArray_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.fillArray = Occil.fillArray :=
  (Exp.open_lc k e _ (by is_lc)).symm

@[simp] theorem fillArray_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.fillArray : Exp rT) = Occil.fillArray :=
  Exp.closeRec_fresh x _ k (by simp [Occil.fillArray, Exp.fv])

@[simp] theorem readArray_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.readArray = Occil.readArray :=
  (Exp.open_lc k e _ (by is_lc)).symm

@[simp] theorem readArray_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.readArray : Exp rT) = Occil.readArray :=
  Exp.closeRec_fresh x _ k (by simp [Occil.readArray, Exp.fv])

end SampLib.ArraySyntax
