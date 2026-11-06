import SampLib.Samplers.StratifiedCell

/-! Closedness of the Cartesian-cell sampler under repetition. -/

open ProbLang

namespace SampLib.StratifiedCell

theorem stratifiedCell_lc {rT : Type _} :
    (Occil.General.stratifiedCell : Exp rT).IsLocallyClosed := by is_lc

theorem stratifiedCell_fv {rT : Type _} :
    (Occil.General.stratifiedCell : Exp rT).fv = ∅ := by
  simp [Occil.General.stratifiedCell, Exp.fv, RndIntExcRange.rndIntExcRange_fv,
    GeneralIntegerPower.integerPower_fv]

@[simp] theorem stratifiedCell_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.General.stratifiedCell = Occil.General.stratifiedCell :=
  (Exp.open_lc k e _ stratifiedCell_lc).symm

@[simp] theorem stratifiedCell_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.General.stratifiedCell : Exp rT) = Occil.General.stratifiedCell :=
  Exp.closeRec_fresh x _ k (by simp [stratifiedCell_fv])

end SampLib.StratifiedCell

namespace SampLib.Stratified1D

theorem stratified1D_lc {rT : Type _} :
    (Occil.General.stratified1D : Exp rT).IsLocallyClosed := by is_lc

theorem stratified1D_fv {rT : Type _} :
    (Occil.General.stratified1D : Exp rT).fv = ∅ := by
  simp [Occil.General.stratified1D, Exp.fv, RndIntExcRange.rndIntExcRange_fv]

@[simp] theorem stratified1D_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.General.stratified1D = Occil.General.stratified1D :=
  (Exp.open_lc k e _ stratified1D_lc).symm

@[simp] theorem stratified1D_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.General.stratified1D : Exp rT) = Occil.General.stratified1D :=
  Exp.closeRec_fresh x _ k (by simp [stratified1D_fv])

end SampLib.Stratified1D
