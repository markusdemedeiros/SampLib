import SampLib.Discrete.WeightedChoice
import SampLib.Core.ListEncoding
import SampLib.Weighted.Laws.WeightedSelections
import SampLib.Core.SupportedSpec
import SampLib.Core.MarkovTerms
import Samplers.Weighted.Sequential

/-! # Ordered weighted sampling without replacement

Every draw selects a positive-weight label proportionally to the remaining
weights, then zeroes that coordinate. The positive-label count bounds requests.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.WeightedWithoutReplacement

noncomputable section

private theorem valid_test (k available : ℕ) (hk : k ≤ available) :
    decide ((available : ℤ) < k) = false := by
  simp only [decide_eq_false_iff_not]
  omega

private def positive {rT : Type _} : Exp rT := pl%
  rec count xs := case! xs
    | inl(u) => #0
    | inr(p) => (if #0 < fst(p) then #1 else #0) + count (snd(p))

private def setZero {rT : Type _} : Exp rT := pl%
  rec update xs i := case! xs
    | inl(u) => fail
    | inr(p) => if i = #0 then inr((#0, snd(p))) else
      inr((fst(p), update (snd(p)) (i - #1)))

private theorem setZero_lc {rT : Type _} : (setZero : Exp rT).IsLocallyClosed := by is_lc

private theorem setZero_fv {rT : Type _} : (setZero : Exp rT).fv = ∅ := by
  simp [setZero, Exp.fv]

@[local simp] private theorem setZero_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e setZero = setZero := (Exp.open_lc k e _ setZero_lc).symm

@[local simp] private theorem setZero_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (setZero : Exp rT) = setZero :=
  Exp.closeRec_fresh x _ k (by simp [setZero_fv])

@[local simp] private theorem setZero_subst {rT : Type _} (x : Var) (e : Exp rT) :
    Exp.subst setZero x e = setZero :=
  Exp.subst_fresh x _ e (by simp [setZero_fv])

private def loop {rT : Type _} : Exp rT :=
  Exp.subst (Exp.subst (pl% rec draw ws remaining :=
    if remaining = #0 then inl(#()) else
      let i := choose ws;
      inr((i, draw (zero ws i) (remaining - #1))))
    (.named "zero") setZero) (.named "choose") Occil.weightedChoice

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_positive (E : CoPset) (ws : List ℕ) :
    ⊢ tglWp E pl(&positive &(listVal (fun i : ℕ => Val.int i) ws).fst)
      (fun v => iprop(⌜v = Val.int (WeightedSelections.positiveCount ws : ℤ)⌝)) := by
  induction ws with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    itrivial
  | cons w ws ih =>
    simp only [listVal]
    iterate 5 twp_pure
    twp_bind pl(&positive &(listVal (fun i : ℕ => Val.int i) ws).fst)
    iapply tglWp_wand
    isplitl []
    · iapply ih
    iintro %v %hv
    subst v
    twp_pures
    by_cases hw : 0 < w
    · rw [show decide ((0 : ℤ) < (w : ℤ)) = true by exact_mod_cast decide_eq_true hw]
      twp_pures
      twp_value
      imodintro
      ipureintro
      apply Val.ext
      simp [WeightedSelections.positiveCount_cons, hw]
    · rw [show decide ((0 : ℤ) < (w : ℤ)) = false by exact decide_eq_false (by omega)]
      twp_pures
      twp_value
      imodintro
      ipureintro
      apply Val.ext
      simp [WeightedSelections.positiveCount_cons, hw]

private theorem twp_setZero (E : CoPset) (ws : List ℕ) (i : Fin ws.length) :
    ⊢ tglWp E pl(&setZero &(listVal (fun j : ℕ => Val.int j) ws).fst #int (i.val : ℤ))
      (fun v => iprop(⌜v = listVal (fun j : ℕ => Val.int j) (ws.set i.val 0)⌝)) := by
  induction ws with
  | nil => exact Fin.elim0 i
  | cons w ws ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [listVal]
      twp_pures
      change ⊢ tglWp E (Exp.ofVal (listVal (fun j : ℕ => Val.int j) (0 :: ws))) _
      iapply (tglWp_value (v := listVal (rT := rT) (fun j : ℕ => Val.int j) (0 :: ws)))
      itrivial
    · simp only [listVal]
      iterate 9 twp_pure
      rw [Fin.val_succ, Nat.cast_add_one, add_sub_cancel_right]
      twp_bind pl(&setZero &(listVal (fun j : ℕ => Val.int j) ws).fst #int (i.val : ℤ))
      iapply tglWp_wand
      isplitl []
      · iapply ih i
      iintro %v %hv
      subst v
      twp_pures
      change ⊢ tglWp E
        (Exp.ofVal (listVal (fun j : ℕ => Val.int j) (w :: ws.set i.val 0))) _
      iapply (tglWp_value
        (v := listVal (rT := rT) (fun j : ℕ => Val.int j) (w :: ws.set i.val 0)))
      itrivial

variable [ProbLangDist.IsUniformInt rT]

private theorem twp_loop (E : CoPset) (ws : List ℕ) (k : ℕ)
    (hk : k ≤ WeightedSelections.positiveCount ws) (F : List ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ is, F is ∂WeightedSelections.law ws k) -∗
      tglWp E pl(&loop &(listVal (fun i : ℕ => Val.int i) ws).fst #int (k : ℤ))
        (fun v => iprop(∃ is : List ℕ,
          ⌜v = listVal (fun i : ℕ => Val.int i) is⌝ ∗ ↯ (F is))) := by
  induction k generalizing ws F with
  | zero =>
    iintro Hcredit
    simp [loop, Exp.subst, Exp.close, Exp.closeRec]
    twp_pures
    twp_value
    imodintro
    iexists []
    iframe Hcredit
    ipureintro
    exact Val.ext rfl
  | succ k ih =>
    have hs := WeightedSelections.positive_of_request ws k hk
    let : NeZero ws.sum := ⟨hs.ne'⟩
    iintro Hcredit
    simp [loop, Exp.subst, Exp.close, Exp.closeRec]
    iterate 5 twp_pure
    simp only [MarkovTerms.weightedChoice_openRec]
    twp_bind pl(&Occil.weightedChoice &(listVal (fun i : ℕ => Val.int i) ws).fst)
    isimp only [← WeightedSelections.expectation ws hs k F] at Hcredit
    iapply ((WeightedChoice.weightedChoice_distSpec E ws).wp_supported
      (fun i => 0 < ws[i]?.getD 0) (Set.to_countable _).measurableSet
      (WeightedChoice.ae_pos_weight ws) (WeightedSelections.continuation ws k F)
      (measurable_of_countable _) _) $$ Hcredit
    iintro %i %hi Hcredit
    iterate 2 twp_pure
    rw [add_sub_cancel_right]
    simp only [setZero_openRec]
    twp_bind pl(&setZero &(listVal (fun j : ℕ => Val.int j) ws).fst #int (i : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply twp_setZero E ws ⟨i, WeightedSelections.index_lt ws i hi⟩
    iintro %v %hv
    subst v
    simp only [Exp.ofVal, MarkovTerms.weightedChoice_openRec]
    twp_bind pl(&loop &(listVal (fun j : ℕ => Val.int j) (ws.set i 0)).fst
      #int (k : ℤ))
    iapply tglWp_wand
    isplitl [Hcredit]
    · isimp only [WeightedSelections.continuation] at Hcredit
      iapply ih (ws.set i 0) (WeightedSelections.remaining_bound ws i k hi hk)
        (fun is => F (i :: is)) $$ Hcredit
    iintro %v ⟨%is, %hv, Hcredit⟩
    subst v
    simp only [Exp.ofVal]
    iapply (tglWp_value_of_toVal (Val.toVal?_fst (Val.inr (.pair (.int (i : ℤ))
      (listVal (rT := rT) (fun j : ℕ => Val.int j) is)))))
    iexists i :: is
    iframe Hcredit
    ipureintro
    exact Val.ext rfl

/-- Ordered PPS sampling, for every request bounded by the positive-weight count. -/
theorem weightedWithoutReplacement_distSpec (E : CoPset) (ws : List ℕ) (k : ℕ)
    (hk : k ≤ WeightedSelections.positiveCount ws) :
    IsDistSpec (GF := GF) E pl(&Occil.weightedWithoutReplacement
      &(listVal (fun i : ℕ => Val.int i) ws).fst #int (k : ℤ))
      (WeightedSelections.law ws k) (listVal (fun i : ℕ => Val.int i)) := by
  refine ⟨fun F _ => ?_⟩
  have hloop := twp_loop (rT := rT) (GF := GF) E ws k hk F
  simp [loop, setZero, Exp.subst, Exp.close, Exp.closeRec] at hloop
  iintro Hcredit
  iterate 4 twp_pure
  twp_bind pl(&positive &(listVal (fun i : ℕ => Val.int i) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_positive E ws
  iintro %v %hv
  subst v
  twp_pures
  simp only [Bool.false_or]
  rw [valid_test k _ hk]
  iterate 2 twp_pure
  simp only [MarkovTerms.weightedChoice_openRec, MarkovTerms.weightedChoice_closeRec]
  iapply hloop $$ Hcredit

end specification

end

end SampLib.WeightedWithoutReplacement
