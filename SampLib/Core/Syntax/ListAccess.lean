import SampLib.Core.ListEncoding
import Samplers.General.Core

/-! Closed map and lookup routines under point-set binders. -/

open ProbLang

namespace SampLib.ListAccess

theorem getAt_lc {rT : Type _} : (Occil.getAt : Exp rT).IsLocallyClosed := by is_lc

theorem getAt_fv {rT : Type _} : (Occil.getAt : Exp rT).fv = ∅ := by
  simp [Occil.getAt, Exp.fv]

@[simp] theorem getAt_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.getAt = Occil.getAt := (Exp.open_lc k e _ getAt_lc).symm

@[simp] theorem getAt_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.getAt : Exp rT) = Occil.getAt :=
  Exp.closeRec_fresh x _ k (by simp [getAt_fv])

theorem map_lc {rT : Type _} : (Occil.General.map : Exp rT).IsLocallyClosed := by is_lc

theorem map_fv {rT : Type _} : (Occil.General.map : Exp rT).fv = ∅ := by
  simp [Occil.General.map, Exp.fv]

@[simp] theorem map_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.General.map = Occil.General.map := (Exp.open_lc k e _ map_lc).symm

@[simp] theorem map_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.General.map : Exp rT) = Occil.General.map :=
  Exp.closeRec_fresh x _ k (by simp [map_fv])

end SampLib.ListAccess
