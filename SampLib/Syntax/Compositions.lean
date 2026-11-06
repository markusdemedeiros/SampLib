import SampLib.IntegerRange
import SampLib.Samplers.SampleInOrder

/-! Closedness of the subset and composition constructors. -/

open ProbLang

namespace SampLib.SampleInOrder

theorem sampleInOrder_lc {rT : Type _} :
    (Occil.sampleInOrder : Exp rT).IsLocallyClosed := by is_lc

theorem sampleInOrder_fv {rT : Type _} : (Occil.sampleInOrder : Exp rT).fv = ∅ := by
  simp [Occil.sampleInOrder, Occil.length, Occil.uniformInt, Exp.fv]

@[simp] theorem sampleInOrder_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.sampleInOrder = Occil.sampleInOrder :=
  (Exp.open_lc k e _ sampleInOrder_lc).symm

@[simp] theorem sampleInOrder_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.sampleInOrder : Exp rT) = Occil.sampleInOrder :=
  Exp.closeRec_fresh x _ k (by simp [sampleInOrder_fv])

end SampLib.SampleInOrder

namespace SampLib.PositiveComposition

theorem positiveComposition_lc {rT : Type _} :
    (Occil.positiveComposition : Exp rT).IsLocallyClosed := by is_lc

theorem positiveComposition_fv {rT : Type _} : (Occil.positiveComposition : Exp rT).fv = ∅ := by
  simp [Occil.positiveComposition, Exp.fv, SampleInOrder.sampleInOrder_fv,
    IntegerRange.intRange_fv]

@[simp] theorem positiveComposition_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.positiveComposition = Occil.positiveComposition :=
  (Exp.open_lc k e _ positiveComposition_lc).symm

@[simp] theorem positiveComposition_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.positiveComposition : Exp rT) = Occil.positiveComposition :=
  Exp.closeRec_fresh x _ k (by simp [positiveComposition_fv])

end SampLib.PositiveComposition
