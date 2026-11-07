import SampLib.Weighted.Laws.EnvelopeRejection
import SampLib.Core.Retry
import SampLib.Discrete.WeightedChoice
import SampLib.Uniform.RationalCoin
import Samplers.Weighted.Sequential

/-! # Integer-envelope categorical rejection

Uniform category proposals are accepted with probability weight/envelope.
The accepted law is categorical; rejected proposals carry amplified retry credit.
-/

open ProbLang Finset
open scoped ENNReal NNReal

namespace SampLib.WeightedRejection

noncomputable section

private theorem nonpositive_test (n : ℕ) (hn : 0 < n) :
    decide ((n : ℤ) ≤ 0) = false := decide_eq_false (by omega)

private def valid {rT : Type _} (m : ℕ) : Exp rT := pl%
  rec check xs := case! xs | inl(u) => #true | inr(p) =>
    if (fst(p) < #0) || (#int (m : ℤ) < fst(p)) then #false else check (snd(p))

private def loop {rT : Type _} [ProbLangℝ rT] (ws : List ℕ) (m : ℕ) : Exp rT := pl%
  rec draw u :=
    let i := &Occil.uniformInt (&Occil.length &(listVal (fun n : ℕ => Val.int n) ws).fst);
    if &Occil.rationalCoin
        (&Occil.getAt &(listVal (fun n : ℕ => Val.int n) ws).fst i) #int (m : ℤ)
    then i else draw #()

private theorem length_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.length = Occil.length :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem length_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.length : Exp rT) = Occil.length :=
  Exp.closeRec_fresh x _ k (by simp [Occil.length, Exp.fv])

private theorem getAt_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.getAt = Occil.getAt :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem getAt_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.getAt : Exp rT) = Occil.getAt :=
  Exp.closeRec_fresh x _ k (by simp [Occil.getAt, Exp.fv])

private theorem list_close {rT : Type _} [ProbLangℝ rT] (ws : List ℕ) (k : ℕ) (x : Var) :
    Exp.closeRec k x (listVal (fun n : ℕ => (Val.int n : Val rT)) ws).fst =
      (listVal (fun n : ℕ => Val.int n) ws).fst := by
  induction ws with
  | nil => rfl
  | cons w ws IH =>
    change Exp.inr (Exp.pair (.lit (.int _))
      (Exp.closeRec k x (listVal (fun n : ℕ => Val.int n) ws).fst)) = _
    rw [IH]
    rfl

attribute [local simp] list_close length_close getAt_close

private theorem loop_lc {rT : Type _} [ProbLangℝ rT] (ws : List ℕ) (m : ℕ) :
    (loop (rT := rT) ws m).IsLocallyClosed := by
  unfold loop
  is_lc

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_valid (E : CoPset) (ws : List ℕ) (m : ℕ)
    (hbound : ∀ w ∈ ws, w ≤ m) :
    ⊢ tglWp E pl(&(valid (rT := rT) m) &(listVal (fun n : ℕ => Val.int n) ws).fst)
      (fun v : Val rT => iprop(⌜v = Val.bool true⌝)) := by
  induction ws with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    itrivial
  | cons w ws IH =>
    have hw : (w : ℤ) ≤ m := by exact_mod_cast hbound w (by simp)
    have htail : ∀ x ∈ ws, x ≤ m := fun x hx => hbound x (by simp [hx])
    simp only [listVal]
    iterate 6 twp_pure
    simp only [not_lt.mpr hw, decide_false]
    iterate 5 twp_pure
    exact IH htail

private theorem twp_loop (E : CoPset) (ws : List ℕ) (m : ℕ)
    (hs : 0 < ws.sum) (hm : 0 < m) (hbound : ∀ w ∈ ws, w ≤ m)
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) -∗
      tglWp (rT := rT) (GF := GF) E pl(&(loop (rT := rT) ws m) #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ ↯ (F i))) := by
  have hn := List.length_pos_of_sum_ne_zero ws hs.ne'
  have hlooplc := loop_lc (rT := rT) ws m
  iapply Retry.twp_loop solve_not_value (EnvelopeRejection.one_lt_factor ws m hn hm)
  iintro !> %ε %hε IH Hcredit
  twp_pure
  simp only [list_close]
  twp_pure
  simp only [length_open, length_close, getAt_open, getAt_close,
    UniformInt.uniformInt_openRec, UniformInt.uniformInt_closeRec,
    RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec]
  twp_bind pl(&Occil.length &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_length E _ ws
  iintro %v %hv
  subst v
  twp_bind pl(&Occil.uniformInt #int (ws.length : ℤ))
  ihave Hsample := ErrorCredit.weaken (expectation ws m hs hm hbound F ε) $$ Hcredit
  iapply tglWp_wand
  isplitl [Hsample]
  · iapply (UniformInt.twp_uniformInt E ws.length hn (proposalCredit ws m F ε)) $$ Hsample
  iintro %v ⟨%i, %hv, %hi, Hcredit⟩
  subst v
  twp_pure
  simp only [length_open, getAt_open, UniformInt.uniformInt_openRec,
    RationalCoin.rationalCoin_openRec]
  twp_bind pl(&Occil.getAt &(listVal (fun n : ℕ => Val.int n) ws).fst #int (i : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_getAt E _ ws ⟨i, hi⟩
  iintro %v %hv
  subst v
  twp_bind pl(&Occil.rationalCoin #int (ws.get ⟨i, hi⟩ : ℤ) #int (m : ℤ))
  isimp only [← EnvelopeRejection.coin_expectation ws m hm hbound F ε ⟨i, hi⟩] at Hcredit
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply (RationalCoin.twp_rationalCoin E (ws.get ⟨i, hi⟩) m
      (Int.natCast_nonneg _) (Int.natCast_pos.mpr hm)
      (Int.ofNat_le.mpr (hbound _ (List.get_mem ..)))
      (coinCredit ws m F ε i)) $$ Hcredit
  iintro %v ⟨%b, %hv, Hcredit⟩
  subst v
  cases b
  · twp_pure
    isimp only [coinCredit, Bool.false_eq_true, ite_false] at Hcredit
    isimp [loop, Exp.close, Exp.closeRec] at IH
    iapply IH $$ Hcredit
  · twp_pures
    twp_value
    imodintro
    iexists i
    isimp only [coinCredit, ite_true] at Hcredit
    iframe Hcredit
    itrivial

/-- CTE specification for every nonnegative weight list with positive total. -/
theorem twp_weightedRejection (E : CoPset) (ws : List ℕ) (m : ℕ)
    (hs : 0 < ws.sum) (hm : 0 < m) (hbound : ∀ w ∈ ws, w ≤ m)
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) -∗
      tglWp E pl(&Occil.weightedRejection
        &(listVal (fun n : ℕ => Val.int n) ws).fst #int (m : ℤ))
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ ↯ (F i))) := by
  have hloop := twp_loop (rT := rT) (GF := GF) E ws m hs hm hbound F
  simp [loop, Exp.close, Exp.closeRec] at hloop
  iintro Hcredit
  iterate 3 twp_pure
  simp only [length_close, length_open, getAt_close, getAt_open,
    UniformInt.uniformInt_openRec, UniformInt.uniformInt_closeRec,
    RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec]
  twp_bind pl(&Occil.sumInts &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedChoice.twp_sumInts E ws
  iintro %v %hv
  subst v
  twp_pures
  simp only [nonpositive_test m hm, nonpositive_test ws.sum hs, Bool.or_false]
  twp_pure
  twp_bind pl(&(valid (rT := rT) m) &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_valid E ws m hbound
  iintro %v %hv
  subst v
  twp_pure
  twp_pure
  iapply hloop
  iexact Hcredit

/-- Exact categorical output law, independent of the chosen valid envelope. -/
theorem weightedRejection_distSpec (E : CoPset) (ws : List ℕ) (m : ℕ)
    (hs : 0 < ws.sum) (hm : 0 < m) (hbound : ∀ w ∈ ws, w ≤ m) :
    letI : NeZero ws.sum := ⟨hs.ne'⟩
    IsDistSpec (GF := GF) E pl(&Occil.weightedRejection
      &(listVal (fun n : ℕ => Val.int n) ws).fst #int (m : ℤ))
      (WeightedChoice.law ws) (fun i => Val.int (i : ℤ)) := by
  have : NeZero ws.sum := ⟨hs.ne'⟩
  exact ⟨fun F _ => wand_entails (twp_weightedRejection E ws m hs hm hbound F)⟩

end specification

end

end SampLib.WeightedRejection
