import SampLib.WeightedValidation
import SampLib.Syntax.Arrays
import Samplers.Weighted.Aliases

/-! # Closed alias-table routines under sampler binders -/

open ProbLang

namespace SampLib.AliasSyntax

theorem voseTable_lc {rT : Type _} :
    (Occil.WeightedVariants.voseTable : Exp rT).IsLocallyClosed := by is_lc

theorem voseTable_fv {rT : Type _} :
    (Occil.WeightedVariants.voseTable : Exp rT).fv = ∅ := by
  simp [Occil.WeightedVariants.voseTable, Exp.fv, WeightedValidation.validWeights_fv,
    WeightedValidation.sumInts_fv, Occil.length]

@[simp] theorem voseTable_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.WeightedVariants.voseTable = Occil.WeightedVariants.voseTable :=
  (Exp.open_lc k e _ voseTable_lc).symm

@[simp] theorem voseTable_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.WeightedVariants.voseTable : Exp rT) =
      Occil.WeightedVariants.voseTable :=
  Exp.closeRec_fresh x _ k (by simp [voseTable_fv])

theorem voseDraw_lc {rT : Type _} :
    (Occil.WeightedVariants.voseDraw : Exp rT).IsLocallyClosed := by is_lc

theorem voseDraw_fv {rT : Type _} :
    (Occil.WeightedVariants.voseDraw : Exp rT).fv = ∅ := by
  simp [Occil.WeightedVariants.voseDraw, Exp.fv, UniformInt.uniformInt_fv]

@[simp] theorem voseDraw_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.WeightedVariants.voseDraw = Occil.WeightedVariants.voseDraw :=
  (Exp.open_lc k e _ voseDraw_lc).symm

@[simp] theorem voseDraw_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.WeightedVariants.voseDraw : Exp rT) =
      Occil.WeightedVariants.voseDraw :=
  Exp.closeRec_fresh x _ k (by simp [voseDraw_fv])

end SampLib.AliasSyntax
