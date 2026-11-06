import SampLib.Combinatorial.Laws.RandomGraph
import SampLib.Core.ListEncoding
import Samplers.Combinatorial.Basic

/-! # Independent-edge random graphs

The nested loops visit the canonical upper triangle in lexicographic order. Each
fresh callback draw retains one edge, giving the product Bernoulli graph law.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.RandomGraph

noncomputable section

def edgeVal {rT : Type _} (e : Edge) : Val rT :=
  .pair (.int (e.1 : ℤ)) (.int (e.2 : ℤ))

-- Finalized binders keep arbitrary callback free variables outside the closing operation.
@[pl_fold] private def outer {rT : Type _} (n : ℕ) (coin : Val rT) : Exp rT :=
  .fix (.lam (.cond (.binop .le (.lit (.int n)) (.bvar 0)) (.inl (.lit .unit))
    (.app (.lam (.app (.bvar 0) (.binop .plus (.bvar 1) (.lit (.int 1)))))
      (.fix (.lam (.cond (.binop .le (.lit (.int n)) (.bvar 0))
        (.app (.bvar 3) (.binop .plus (.bvar 2) (.lit (.int 1))))
        (.cond (.app coin.fst (.lit .unit))
          (.inr (.pair (.pair (.bvar 2) (.bvar 0))
            (.app (.bvar 1) (.binop .plus (.bvar 0) (.lit (.int 1))))))
          (.app (.bvar 1) (.binop .plus (.bvar 0) (.lit (.int 1)))))))))))

private theorem outer_openRec {rT : Type _} (n : ℕ) (coin : Val rT)
    (k : ℕ) (v : Exp rT) : Exp.openRec k v (outer n coin) = outer n coin :=
  (Exp.open_lc k v (outer n coin) (by is_lc)).symm

@[pl_fold] private def inner {rT : Type _} (n : ℕ) (coin : Val rT) (i : ℕ) : Exp rT :=
  .fix (.lam (.cond (.binop .le (.lit (.int n)) (.bvar 0))
    (.app (outer n coin) (.binop .plus (.lit (.int i)) (.lit (.int 1))))
    (.cond (.app coin.fst (.lit .unit))
      (.inr (.pair (.pair (.lit (.int i)) (.bvar 0))
        (.app (.bvar 1) (.binop .plus (.bvar 0) (.lit (.int 1))))))
      (.app (.bvar 1) (.binop .plus (.bvar 0) (.lit (.int 1)))))))

private theorem edgeVal_cons {rT : Type _} [ProbLangℝ rT] (i j : ℕ) (ys : List Edge) :
    pl(inr(((#int (i : ℤ), #int (j : ℤ)), {Exp.ofVal (listVal edgeVal ys)}))) =
      Exp.ofVal (listVal edgeVal ((i, j) :: ys) : Val rT) := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open MeasureTheory

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] outer_openRec

private theorem inner_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (n i : ℕ) (rest : List Edge)
    (hnext : IsDistSpec (GF := GF) E pl(&(outer n coin) #int ((i + 1 : ℕ) : ℤ))
      (law p rest) (listVal edgeVal))
    (j r : ℕ) (hn : n = j + r) :
    IsDistSpec (GF := GF) E pl(&(inner n coin i) #int (j : ℤ))
      (law p (columns i j r ++ rest)) (listVal edgeVal) := by
  induction r generalizing j with
  | zero =>
    have hle : (n : ℤ) ≤ (j : ℤ) := by omega
    constructor
    intro F _
    iintro Hcredit
    isimp only [columns, List.nil_append] at Hcredit
    iterate 3 twp_pure
    simp only [hle, _root_.decide_true]
    twp_pure
    twp_pure
    rw [← Nat.cast_add_one]
    twp_bind pl(&(outer n coin) #int ((i + 1 : ℕ) : ℤ))
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply hnext.spec F (measurable_of_countable _) $$ Hcredit
  | succ r IH =>
    have hlt : ¬(n : ℤ) ≤ (j : ℤ) := by omega
    have hn' : n = (j + 1) + r := by omega
    constructor
    intro F _
    iintro Hcredit
    isimp only [columns, List.cons_append, ← expectation] at Hcredit
    iterate 3 twp_pure
    simp only [hlt, _root_.decide_false]
    twp_pure
    twp_bind pl(&coin.fst #())
    iapply (hcoin.wp (credit p (i, j) (columns i (j + 1) r ++ rest) F)
      (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    cases b
    · isimp only [credit, Bool.false_eq_true, ite_false] at Hcredit
      twp_pure
      twp_pure
      rw [← Nat.cast_add_one]
      twp_bind pl(&(inner n coin i) #int ((j + 1 : ℕ) : ℤ))
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply (IH (j + 1) hn').spec F (measurable_of_countable _) $$ Hcredit
    · isimp only [credit, ite_true] at Hcredit
      twp_pure
      twp_pure
      rw [← Nat.cast_add_one]
      twp_bind pl(&(inner n coin i) #int ((j + 1 : ℕ) : ℤ))
      iapply tglWp_wand
      isplitl [Hcredit]
      · iapply (IH (j + 1) hn').spec (fun ys => F ((i, j) :: ys))
          (measurable_of_countable _) $$ Hcredit
      iintro %v ⟨%ys, %hv, Hcredit⟩
      subst v
      rw [edgeVal_cons]
      iapply (tglWp_value (v := listVal edgeVal ((i, j) :: ys)))
      iexists ((i, j) :: ys)
      iframe Hcredit
      itrivial

private theorem outer_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (n i m : ℕ) (hn : n = i + m) :
    IsDistSpec (GF := GF) E pl(&(outer n coin) #int (i : ℤ))
      (law p (edges i m)) (listVal edgeVal) := by
  induction m generalizing i with
  | zero =>
    have heq : n = i := by omega
    constructor
    intro F _
    iintro Hcredit
    isimp only [edges, expectation_nil] at Hcredit
    iterate 3 twp_pure
    simp only [heq, le_refl, _root_.decide_true]
    twp_pure
    twp_value
    imodintro
    iexists []
    iframe Hcredit
    ipureintro
    exact Val.ext rfl
  | succ m IH =>
    have hlt : ¬(n : ℤ) ≤ (i : ℤ) := by omega
    have hn' : n = (i + 1) + m := by omega
    constructor
    intro F _
    iintro Hcredit
    iterate 3 twp_pure
    simp only [hlt, _root_.decide_false]
    twp_pure
    twp_pure
    twp_pure
    rw [← Nat.cast_add_one]
    change ↯ (∫⁻ ys, F ys ∂law p (columns i (i + 1) m ++ edges (i + 1) m)) ⊢
      tglWp E pl(&(inner n coin i) #int ((i + 1 : ℕ) : ℤ)) _
    exact (inner_distSpec E p coin hcoin n i (edges (i + 1) m) (IH (i + 1) hn')
      (i + 1) m hn').spec F (measurable_of_countable _)

/-- The direct independent-edge graph sampler, with full deterministic endpoints. -/
theorem randomGraph_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (n : ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.randomGraph #int (n : ℤ) &coin.fst)
      (law p (complete n)) (listVal edgeVal) where
  spec F _ := by
    iintro Hcredit
    iterate 5 twp_pure
    change ↯ (∫⁻ ys, F ys ∂law p (edges 0 n)) ⊢
      tglWp E pl(&(outer n coin) #0) _
    exact (outer_distSpec E p coin hcoin n 0 n (zero_add n).symm).spec F
      (measurable_of_countable _)

end specification

end

end SampLib.RandomGraph
