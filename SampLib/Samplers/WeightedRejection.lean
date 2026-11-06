import SampLib.Samplers.WeightedChoice
import SampLib.Samplers.RationalCoin
import Samplers.Weighted.Sequential

/-! # Integer-envelope categorical rejection

Uniform category proposals are accepted with probability weight/envelope.
The accepted law is categorical; rejected proposals carry amplified retry credit.
-/

open ProbLang Finset
open scoped ENNReal NNReal

set_option maxHeartbeats 800000

namespace SampLib.WeightedRejection

noncomputable section

section mathematics

open MeasureTheory

/-- Unused portions of the category envelopes. -/
def spare (ws : List ℕ) (m : ℕ) : ℕ := (ws.map (m - ·)).sum

private theorem total_envelope (ws : List ℕ) (m : ℕ) (h : ∀ w ∈ ws, w ≤ m) :
    ws.sum + spare ws m = ws.length * m := by
  induction ws with
  | nil => simp [spare]
  | cons w ws IH =>
    have hw := h w (by simp)
    have ht := IH (fun x hx => h x (by simp [hx]))
    simp only [List.sum_cons, spare, List.map_cons, List.sum_cons, List.length_cons] at *
    nlinarith [Nat.sub_add_cancel hw]

private theorem length_pos (ws : List ℕ) (hs : 0 < ws.sum) : 0 < ws.length := by
  by_contra h
  have hz : ws = [] := List.length_eq_zero_iff.mp (by omega)
  simp [hz] at hs

private theorem nonpositive_test (n : ℕ) (hn : 0 < n) :
    decide ((n : ℤ) ≤ 0) = false := decide_eq_false (by omega)

/-- A bounded amplification factor, valid even when every proposal succeeds. -/
def factor (ws : List ℕ) (m : ℕ) : ℝ≥0 :=
  1 + (ws.length * m : ℝ≥0)⁻¹

private theorem one_lt_factor (ws : List ℕ) (m : ℕ) (hn : 0 < ws.length) (hm : 0 < m) :
    1 < factor ws m := by
  apply lt_add_of_pos_right
  exact inv_pos.mpr (by positivity)

/-- Continuation credits after the acceptance coin. -/
def coinCredit (ws : List ℕ) (m : ℕ) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞)
    (i : ℕ) (b : Bool) : ℝ≥0∞ :=
  if b then F i else (∫⁻ i, F i ∂WeightedChoice.law ws) + factor ws m * ε

/-- Credit for a uniform proposal, written directly with integer envelope widths. -/
def proposalCredit (ws : List ℕ) (m : ℕ) (F : ℕ → ℝ≥0∞)
    (ε : ℝ≥0∞) (i : ℕ) : ℝ≥0∞ :=
  (ws[i]?.getD 0 * F i + (m - ws[i]?.getD 0 : ℕ) *
    ((∫⁻ i, F i ∂WeightedChoice.law ws) + factor ws m * ε)) / m

private theorem sum_widths (ws : List ℕ) (m : ℕ) (F : ℕ → ℝ≥0∞) (R : ℝ≥0∞) :
    ∑ i ∈ range ws.length, ((ws[i]?.getD 0 : ℝ≥0∞) * F i +
      (m - ws[i]?.getD 0 : ℕ) * R) = WeightedChoice.weightedSum ws F + spare ws m * R := by
  induction ws generalizing F with
  | nil => simp [WeightedChoice.weightedSum, spare]
  | cons w ws IH =>
    rw [List.length_cons, sum_range_succ']
    simp only [List.getElem?_cons_zero, Option.getD_some, List.getElem?_cons_succ]
    rw [IH]
    simp only [WeightedChoice.weightedSum, spare, List.map_cons, List.sum_cons, Nat.cast_add]
    ring

/-- Accepted widths give categorical credit; unused widths fund the retry. -/
theorem expectation (ws : List ℕ) (m : ℕ) (hs : 0 < ws.sum) (hm : 0 < m)
    (hbound : ∀ w ∈ ws, w ≤ m) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∑ i ∈ range ws.length, proposalCredit ws m F ε i) / ws.length ≤
      (∫⁻ i, F i ∂WeightedChoice.law ws) + ε := by
  have htotal := total_envelope ws m hbound
  have hn := length_pos ws hs
  have hd : (ws.length * m : ℝ≥0∞) ≠ 0 := by positivity
  have hdt : (ws.length * m : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by finiteness
  have hs0 : (ws.sum : ℝ≥0∞) ≠ 0 := by positivity
  have hsT : (ws.sum : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by finiteness
  let C := ∫⁻ i, F i ∂WeightedChoice.law ws
  have hw : WeightedChoice.weightedSum ws F = ws.sum * C := by
    dsimp [C]
    rw [WeightedChoice.lintegral_law, ENNReal.mul_div_cancel hs0 hsT]
  have hparts : (ws.sum : ℝ≥0∞) / (ws.length * m) +
      spare ws m / (ws.length * m) = 1 := by
    rw [ENNReal.div_add_div_same, ← Nat.cast_add, htotal, Nat.cast_mul,
      ENNReal.div_self hd hdt]
  have hamp : (spare ws m : ℝ≥0∞) / (ws.length * m) * factor ws m ≤ 1 := by
    rw [ENNReal.coe_nnreal_eq]
    have hD : (0 : ℝ) < ws.length * m := by positivity
    have hb : (spare ws m : ℝ) * (1 + ((ws.length : ℝ) * m)⁻¹) /
        (ws.length * m) ≤ 1 := by
      have ht : (ws.sum : ℝ) + spare ws m = (ws.length : ℝ) * m := by
        exact_mod_cast htotal
      have hp : (1 : ℝ) ≤ ws.sum := by exact_mod_cast hs
      rw [div_le_one hD]
      field_simp
      nlinarith
    have he : (spare ws m : ℝ≥0∞) / (ws.length * m) *
        ENNReal.ofReal (factor ws m : ℝ) =
        ENNReal.ofReal ((spare ws m : ℝ) * (1 + ((ws.length : ℝ) * m)⁻¹) /
          (ws.length * m)) := by
      rw [ENNReal.ofReal_div_of_pos hD,
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ spare ws m)]
      simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ws.length)]
      change _ = _ * ENNReal.ofReal (factor ws m : ℝ) / _
      rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
      ring
    rw [he]
    exact ENNReal.ofReal_le_one.mpr hb
  calc
    _ = ((ws.sum : ℝ≥0∞) / (ws.length * m) + spare ws m / (ws.length * m)) * C +
        (spare ws m / (ws.length * m) * (factor ws m : ℝ≥0∞)) * ε := by
      simp only [proposalCredit]
      rw [← ENNReal.sum_div, sum_widths, hw]
      simp only [ENNReal.div_eq_inv_mul]
      rw [ENNReal.mul_inv (Or.inl (by positivity : (ws.length : ℝ≥0∞) ≠ 0))
        (Or.inl (by finiteness : (ws.length : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)))]
      dsimp [C]
      ring
    _ ≤ C + ε := by
      rw [hparts, one_mul]
      exact add_le_add le_rfl (mul_le_of_le_one_left' hamp)

private theorem coin_expectation (ws : List ℕ) (m : ℕ) (hm : 0 < m)
    (hbound : ∀ w ∈ ws, w ≤ m) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞)
    (i : Fin ws.length) :
    RealCoin.credit
      (RationalCoin.bias (ws.get i) m (by positivity) (by exact_mod_cast hm)
        (by exact_mod_cast hbound _ (List.get_mem ..))) (coinCredit ws m F ε i) =
      proposalCredit ws m F ε i := by
  have hw : ws.get i ≤ m := hbound _ (List.get_mem ..)
  have hmR : (0 : ℝ) < m := by positivity
  have hcomp : 1 - (ws.get i : ℝ) / m = ((m - ws.get i : ℕ) : ℝ) / m := by
    rw [Nat.cast_sub hw]
    field_simp
  simp only [RealCoin.credit, RealCoin.pmf, RationalCoin.bias, coinCredit,
    Bool.false_eq_true, ite_true, ite_false, proposalCredit, Int.cast_natCast]
  rw [hcomp]
  rw [List.get_eq_getElem]
  simp only [List.getElem?_eq_getElem i.isLt, Option.getD_some]
  rw [ENNReal.ofReal_div_of_pos hmR, ENNReal.ofReal_div_of_pos hmR]
  simp only [ENNReal.ofReal_natCast]
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  ring

end mathematics

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
  have hn := length_pos ws hs
  have hlooplc := loop_lc (rT := rT) ws m
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε (one_lt_factor ws m hn hm) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
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
  icombine Hcredit Hterm as Htotal
  ihave Hsample := ErrorCredit.weaken (expectation ws m hs hm hbound F ε) $$ Htotal
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
  isimp only [← coin_expectation ws m hm hbound F ε ⟨i, hi⟩] at Hcredit
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
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    isimp [loop, Exp.close, Exp.closeRec] at IH
    iapply IH $$ Hterm Hcredit
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
