import Samplers.Combinatorial.Basic
import Metrology.ProbLang.Syntax.LocallyClosed

/-! # Closed sampler constants under object-language binders -/

open ProbLang

namespace SampLib.SamplerTerms

@[simp] theorem sampleWithReplacement_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.sampleWithReplacement = Occil.sampleWithReplacement :=
  (Exp.open_lc k e _ (by is_lc)).symm

@[simp] theorem sampleWithReplacement_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.sampleWithReplacement : Exp rT) =
      Occil.sampleWithReplacement :=
  Exp.closeRec_fresh x _ k (by
    simp [Occil.sampleWithReplacement, Occil.repeatSample, Occil.choice,
      Occil.length, Occil.getAt, Occil.uniformInt, Exp.fv])

@[simp] theorem rndIntRange_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.rndIntRange = Occil.rndIntRange :=
  (Exp.open_lc k e _ (by is_lc)).symm

@[simp] theorem rndIntRange_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.rndIntRange : Exp rT) = Occil.rndIntRange :=
  Exp.closeRec_fresh x _ k (by
    simp [Occil.rndIntRange, Occil.rndInt, Occil.uniformInt, Exp.fv])

end SampLib.SamplerTerms
