import Samplers.Weighted.Dynamic
import Metrology.ProbLang.Syntax.LocallyClosed

/-! # Closed Fenwick operations under sampler binders -/

open ProbLang

namespace SampLib.FenwickSyntax

theorem newFenwick_lc {rT : Type} :
    (Occil.WeightedVariants.newFenwick : Exp rT).IsLocallyClosed := by is_lc

theorem newFenwick_fv {rT : Type} : (Occil.WeightedVariants.newFenwick : Exp rT).fv = ∅ := by
  simp [Occil.WeightedVariants.newFenwick, Occil.Weighted.validWeights,
    Occil.WeightedVariants.lowBit, Occil.sumInts, Occil.length, Occil.fillArray, Exp.fv]

@[simp] theorem newFenwick_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.WeightedVariants.newFenwick = Occil.WeightedVariants.newFenwick :=
  (Exp.open_lc k e _ newFenwick_lc).symm

@[simp] theorem newFenwick_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.WeightedVariants.newFenwick : Exp rT) =
      Occil.WeightedVariants.newFenwick :=
  Exp.closeRec_fresh x _ k (by simp [newFenwick_fv])

theorem fenwickSet_lc {rT : Type} :
    (Occil.WeightedVariants.fenwickSet : Exp rT).IsLocallyClosed := by is_lc

theorem fenwickSet_fv {rT : Type} : (Occil.WeightedVariants.fenwickSet : Exp rT).fv = ∅ := by
  simp [Occil.WeightedVariants.fenwickSet, Occil.WeightedVariants.lowBit, Exp.fv]

@[simp] theorem fenwickSet_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.WeightedVariants.fenwickSet = Occil.WeightedVariants.fenwickSet :=
  (Exp.open_lc k e _ fenwickSet_lc).symm

@[simp] theorem fenwickSet_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.WeightedVariants.fenwickSet : Exp rT) =
      Occil.WeightedVariants.fenwickSet :=
  Exp.closeRec_fresh x _ k (by simp [fenwickSet_fv])

theorem fenwickDraw_lc {rT : Type} :
    (Occil.WeightedVariants.fenwickDraw : Exp rT).IsLocallyClosed := by is_lc

theorem fenwickDraw_fv {rT : Type} : (Occil.WeightedVariants.fenwickDraw : Exp rT).fv = ∅ := by
  simp [Occil.WeightedVariants.fenwickDraw, Occil.Weighted.powerOfTwoCeiling, Occil.uniformInt,
    Exp.fv]

@[simp] theorem fenwickDraw_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.WeightedVariants.fenwickDraw = Occil.WeightedVariants.fenwickDraw :=
  (Exp.open_lc k e _ fenwickDraw_lc).symm

@[simp] theorem fenwickDraw_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.WeightedVariants.fenwickDraw : Exp rT) =
      Occil.WeightedVariants.fenwickDraw :=
  Exp.closeRec_fresh x _ k (by simp [fenwickDraw_fv])

end SampLib.FenwickSyntax
