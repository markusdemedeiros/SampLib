import SampLib.Core.ListEncoding

/-! Closing integer data under sampler binders. -/

open ProbLang

namespace SampLib.ListValues

theorem listVal_fv {rT : Type _} [ProbLangℝ rT] {α : Type _}
    (encode : α → Val rT) (xs : List α) (h : ∀ x ∈ xs, (encode x).fst.fv = ∅) :
    (listVal encode xs).fst.fv = ∅ := by
  induction xs with
  | nil => rfl
  | cons x xs IH =>
    change (encode x).fst.fv ∪ (listVal encode xs).fst.fv = ∅
    rw [h x (by simp), IH (fun y hy => h y (by simp [hy]))]
    simp

@[simp] theorem listVal_openRec {rT : Type _} [ProbLangℝ rT] {α : Type _}
    (encode : α → Val rT) (xs : List α) (k : ℕ) (e : Exp rT) :
    Exp.openRec k e (listVal encode xs).fst = (listVal encode xs).fst :=
  (Exp.open_lc k e _ (listVal encode xs).lc).symm

theorem intList_fv {rT : Type _} [ProbLangℝ rT] (xs : List ℤ) :
    (listVal (Val.int : ℤ → Val rT) xs).fst.fv = ∅ :=
  listVal_fv _ xs (fun _ _ => rfl)

theorem intMatrix_fv {rT : Type _} [ProbLangℝ rT] (xs : List (List ℤ)) :
    (listVal (listVal (Val.int : ℤ → Val rT)) xs).fst.fv = ∅ :=
  listVal_fv _ xs (fun ys _ => intList_fv ys)

@[simp] theorem intMatrix_closeRec {rT : Type _} [ProbLangℝ rT]
    (xs : List (List ℤ)) (k : ℕ) (x : Var) :
    Exp.closeRec k x (listVal (listVal (Val.int : ℤ → Val rT)) xs).fst =
      (listVal (listVal (Val.int : ℤ → Val rT)) xs).fst :=
  Exp.closeRec_fresh x _ k (by simp [intMatrix_fv])

end SampLib.ListValues
