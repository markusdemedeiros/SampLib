import SampLib.Templates
import Samplers.General.Core

/-! Closedness facts for the concrete calls occurring in finite-state samplers. -/

open ProbLang

namespace SampLib.MarkovTerms

theorem getAt_lc {rT : Type _} : (Occil.getAt : Exp rT).IsLocallyClosed := by is_lc

@[simp] theorem getAt_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.getAt = Occil.getAt :=
  (Exp.open_lc k e _ getAt_lc).symm

@[simp] theorem getAt_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.getAt : Exp rT) = Occil.getAt :=
  Exp.closeRec_fresh x _ k (by simp [Occil.getAt, Exp.fv])

theorem weightedChoice_lc {rT : Type _} :
    (Occil.weightedChoice : Exp rT).IsLocallyClosed := by is_lc

@[simp] theorem weightedChoice_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.weightedChoice = Occil.weightedChoice :=
  (Exp.open_lc k e _ weightedChoice_lc).symm

@[simp] theorem weightedChoice_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.weightedChoice : Exp rT) = Occil.weightedChoice :=
  Exp.closeRec_fresh x _ k
    (by simp [Occil.weightedChoice, Occil.sumInts, Occil.uniformInt, Exp.fv])

theorem markovStep_lc {rT : Type _} :
    (Occil.General.markovStep : Exp rT).IsLocallyClosed := by is_lc

@[simp] theorem markovStep_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.General.markovStep = Occil.General.markovStep :=
  (Exp.open_lc k e _ markovStep_lc).symm

@[simp] theorem markovStep_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.General.markovStep : Exp rT) = Occil.General.markovStep :=
  Exp.closeRec_fresh x _ k
    (by simp [Occil.General.markovStep, Occil.weightedChoice, Occil.sumInts,
      Occil.uniformInt, Occil.getAt, Exp.fv])

end SampLib.MarkovTerms
