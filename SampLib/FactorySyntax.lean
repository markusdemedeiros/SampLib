import SampLib.Samplers.WeightedChoice
import SampLib.Samplers.IterateCoin

/-! # Closed primitive terms used by finite factories -/

open ProbLang

namespace SampLib.FactorySyntax

theorem weightedChoice_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.weightedChoice = Occil.weightedChoice :=
  (Exp.open_lc k e _ (by is_lc)).symm

theorem weightedChoice_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.weightedChoice : Exp rT) = Occil.weightedChoice :=
  Exp.closeRec_fresh x _ k (by
    simp [Occil.weightedChoice, Occil.sumInts, Exp.fv, UniformInt.uniformInt_fv])

theorem iterateCoin_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.iterateCoin = Occil.iterateCoin :=
  (Exp.open_lc k e _ (by is_lc)).symm

theorem iterateCoin_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.iterateCoin : Exp rT) = Occil.iterateCoin :=
  Exp.closeRec_fresh x _ k (by simp [Occil.iterateCoin, Exp.fv])

theorem getAt_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.getAt = Occil.getAt :=
  (Exp.open_lc k e _ (by is_lc)).symm

theorem getAt_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.getAt : Exp rT) = Occil.getAt :=
  Exp.closeRec_fresh x _ k (by simp [Occil.getAt, Exp.fv])

end SampLib.FactorySyntax
