import SampLib.Core.MarkovTerms
import SampLib.Core.SamplerTerms
import SampLib.Core.Syntax.UniformRanges

/-! # Closed list and interval operations in general sampler callbacks -/

open ProbLang

namespace SampLib.GeneralSyntax

@[simp] theorem length_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.length = Occil.length :=
  (Exp.open_lc k e _ (by is_lc)).symm

@[simp] theorem length_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.length : Exp rT) = Occil.length :=
  Exp.closeRec_fresh x _ k (by simp [Occil.length, Exp.fv])

@[simp] theorem map_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.General.map = Occil.General.map :=
  (Exp.open_lc k e _ (by is_lc)).symm

@[simp] theorem map_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.General.map : Exp rT) = Occil.General.map :=
  Exp.closeRec_fresh x _ k (by simp [Occil.General.map, Exp.fv])

export SampLib.RndIntExcRange (rndIntExcRange_openRec rndIntExcRange_closeRec)

@[simp] theorem repeatSample_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.repeatSample = Occil.repeatSample :=
  (Exp.open_lc k e _ (by is_lc)).symm

@[simp] theorem repeatSample_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.repeatSample : Exp rT) = Occil.repeatSample :=
  Exp.closeRec_fresh x _ k (by simp [Occil.repeatSample, Exp.fv])

end SampLib.GeneralSyntax
