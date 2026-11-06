import SampLib.CurriedStep
import SampLib.FactoryFractions
import SampLib.FactoryChoose
import SampLib.Distributions.ReverseBinomial

/-! # The envelope factory's exact conditional average

The reverse-binomial sum uses signed integer subtraction in its second choose
call. Negative indices contribute zero before any coefficient callback is used.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.EnvelopeConditionalAverage

open FactoryFractions

noncomputable section

private def chooseInt (n : ℕ) (k : ℤ) : ℕ :=
  if k < 0 then 0 else n.choose k.toNat

private theorem negative_guard (n : ℕ) (k : ℤ) (hk : k < 0) :
    Bool.or (Bool.or false (decide (k < 0))) (decide ((n : ℤ) < k)) = true := by simp [hk]

/-- Integer weights in the actual signed-index source sum. -/
def weight (n m k j : ℕ) : ℕ :=
  n.choose j * if j ≤ k then (m - n).choose (k - j) else 0

private theorem weight_coefficient (n m k j : ℕ) :
    (weight n m k j : ℚ) / m.choose k = ReverseBinomial.coefficient n m k j := by
  rw [ReverseBinomial.coefficient_eq]
  by_cases hj : j ≤ k <;> simp [weight, hj]

private theorem weight_cast (n m k j : ℕ) :
    (n.choose j : ℤ) * ((if j ≤ k then (m - n).choose (k - j) else 0 : ℕ) : ℤ) =
      (weight n m k j : ℤ) := by simp [weight, Nat.cast_mul]

private def term (raw : ℕ → Bool → Fraction) (n m k : ℕ) (high : Bool) (j : ℕ) : ℚ :=
  (raw j high).value * ReverseBinomial.coefficient n m k j

private theorem term_zero (raw : ℕ → Bool → Fraction) (n m k j : ℕ) (high : Bool)
    (hw : weight n m k j = 0) : term raw n m k high j = 0 := by
  simp only [term, ← weight_coefficient, hw, Nat.cast_zero, zero_div, mul_zero]

private theorem selected (raw : ℕ → Bool → Fraction) (j : ℕ) (high : Bool) :
    (if high then raw j true else raw j false) = raw j high := by cases high <;> rfl

private def sumFrom (raw : ℕ → Bool → Fraction) (n m k : ℕ) (high : Bool)
    (j count : ℕ) : ℚ := ∑ i ∈ Finset.range count, term raw n m k high (j + i)

private theorem sumFrom_succ (raw : ℕ → Bool → Fraction) (n m k : ℕ) (high : Bool)
    (j count : ℕ) : sumFrom raw n m k high j (count + 1) =
      term raw n m k high j + sumFrom raw n m k high (j + 1) count := by
  simp [sumFrom, Finset.sum_range_succ', add_comm, add_left_comm]

/-- Binder-indexed code for the source's exact conditional-average loop. -/
def loopCode {rT : Type} (bounds n m k high denominator : ℕ → Exp rT) : Exp rT :=
  let bind (rhs body : Exp rT) := .app (.lam body) rhs
  let call (f a b : Exp rT) := .app (.app f a) b
  let w := Exp.binop .mult
    (call Occil.FactoryExtra.choose (n 3) (.bvar 1))
    (call Occil.FactoryExtra.choose (.binop .minus (m 3) (n 3))
      (.binop .minus (k 3) (.bvar 1)))
  let skip := call (.bvar 3) (.binop .plus (.bvar 2) pl(#1)) (.bvar 1)
  let previous := call (bounds 4) (n 4) (.bvar 2)
  let coefficient := Exp.cond (high 5) (.snd (.bvar 0)) (.fst (.bvar 0))
  let weighted := call Occil.FactoryExtra.multiplyFraction (.bvar 0)
    (.pair (.bvar 2) (denominator 6))
  let accumulate := call (.bvar 6) (.binop .plus (.bvar 5) pl(#1))
    (call Occil.FactoryExtra.addFraction (.bvar 4) (.bvar 0))
  .fix (.lam (.lam (.cond (.binop .lt (n 3) (.bvar 1)) (.bvar 0)
    (bind w (.cond (.binop .eq (.bvar 0) pl(#0)) skip
      (bind previous (bind coefficient (bind weighted accumulate))))))))

private def loop {rT : Type} (bounds : Val rT) (n m k : ℕ) (high : Bool) : Exp rT :=
  loopCode (fun _ => bounds.fst) (fun _ => pl(#int (n : ℤ)))
    (fun _ => pl(#int (m : ℤ))) (fun _ => pl(#int (k : ℤ)))
    (fun _ => (Val.bool high).fst) (fun _ => pl(#int (m.choose k : ℤ)))

private def stepCode {rT : Type}
    (self bounds n m k high denominator index total : ℕ → Exp rT) : Exp rT :=
  let bind (rhs body : Exp rT) := .app (.lam body) rhs
  let call (f a b : Exp rT) := .app (.app f a) b
  let w := Exp.binop .mult (call Occil.FactoryExtra.choose (n 0) (index 0))
    (call Occil.FactoryExtra.choose (.binop .minus (m 0) (n 0))
      (.binop .minus (k 0) (index 0)))
  let skip := call (self 1) (.binop .plus (index 1) pl(#1)) (total 1)
  let previous := call (bounds 1) (n 1) (index 1)
  let coefficient := Exp.cond (high 2) (.snd (.bvar 0)) (.fst (.bvar 0))
  let weighted := call Occil.FactoryExtra.multiplyFraction (.bvar 0)
    (.pair (.bvar 2) (denominator 3))
  let accumulate := call (self 4) (.binop .plus (index 4) pl(#1))
    (call Occil.FactoryExtra.addFraction (total 4) (.bvar 0))
  .cond (.binop .lt (n 0) (index 0)) (total 0)
    (bind w (.cond (.binop .eq (.bvar 0) pl(#0)) skip
      (bind previous (bind coefficient (bind weighted accumulate)))))

private def loopBody {rT : Type} (bounds : Val rT) (n m k : ℕ) (high : Bool) : Exp rT :=
  match loop bounds n m k high with
  | .fix (.lam (.lam body)) => body
  | _ => .fail

private theorem loopBody_eq {rT : Type} (bounds : Val rT) (n m k : ℕ) (high : Bool) :
    loopBody bounds n m k high = stepCode (fun d => .bvar (d + 2))
      (fun _ => bounds.fst) (fun _ => pl(#int (n : ℤ)))
      (fun _ => pl(#int (m : ℤ))) (fun _ => pl(#int (k : ℤ)))
      (fun _ => (Val.bool high).fst) (fun _ => pl(#int (m.choose k : ℤ)))
      (fun d => .bvar (d + 1)) Exp.bvar := rfl

private def start {rT : Type} : Exp rT :=
  .app (.app (.bvar 0) pl(#0)) pl((#0, #1))

/-- The complete source body, with all external parameters indexed by binder depth. -/
def bodyCode {rT : Type} (bounds n m k high : ℕ → Exp rT) : Exp rT :=
  let average := loopCode (fun depth => bounds (depth + 1))
    (fun depth => n (depth + 1)) (fun depth => m (depth + 1))
    (fun depth => k (depth + 1)) (fun depth => high (depth + 1)) Exp.bvar
  .cond (.binop .eq (n 0) pl(#0)) (.cond (high 0) pl((#1, #1)) pl((#0, #1)))
    (.app (.lam (.app (.lam start) average)) (.app (.app Occil.FactoryExtra.choose (m 0)) (k 0)))

private def afterDenominator {rT : Type} (bounds : Val rT) (n m k : ℕ)
    (high : Bool) : Exp rT :=
  .app (.lam start) (loopCode (fun _ => bounds.fst) (fun _ => pl(#int (n : ℤ)))
    (fun _ => pl(#int (m : ℤ))) (fun _ => pl(#int (k : ℤ)))
    (fun _ => (Val.bool high).fst) Exp.bvar)

/-- The source's `high` body after its surrounding runtime values are supplied. -/
def conditionalBody {rT : Type} (bounds : Val rT) (n m k : ℕ) (high : Bool) : Exp rT :=
  .cond (.binop .eq pl(#int (n : ℤ)) pl(#0))
    (.cond (Val.bool high).fst pl((#1, #1)) pl((#0, #1)))
    (.app (.lam (afterDenominator bounds n m k high))
      pl(&Occil.FactoryExtra.choose #int (m : ℤ) #int (k : ℤ)))

theorem conditionalBody_eq {rT : Type} (bounds : Val rT) (n m k : ℕ) (high : Bool) :
    conditionalBody bounds n m k high = bodyCode (fun _ => bounds.fst)
      (fun _ => pl(#int (n : ℤ))) (fun _ => pl(#int (m : ℤ)))
      (fun _ => pl(#int (k : ℤ))) (fun _ => (Val.bool high).fst) := rfl

/-- Exact conditional rational mean; the initial row is the source's `[0,1]` interval. -/
def mean (raw : ℕ → Bool → Fraction) (n m k : ℕ) (high : Bool) : ℚ :=
  if n = 0 then if high then 1 else 0
  else ∑ j ∈ Finset.range (n + 1), ReverseBinomial.coefficient n m k j * (raw j high).value

def highBody {rT : Type} (bounds : Val rT) (n m k : ℕ) : Exp rT :=
  bodyCode (fun _ => bounds.fst) (fun _ => pl(#int (n : ℤ)))
    (fun _ => pl(#int (m : ℤ))) (fun _ => pl(#int (k : ℤ))) Exp.bvar

private instance choose_closed {rT : Type} :
    ClosedExp (Occil.FactoryExtra.choose : Exp rT) where
  lc := FactoryChoose.choose_lc
  fv := FactoryChoose.choose_fv

private instance multiply_closed {rT : Type} :
    ClosedExp (Occil.FactoryExtra.multiplyFraction : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.FactoryExtra.multiplyFraction, Exp.fv, ClosedExp.closeRec, ClosedExp.fv]

private theorem zero_test (w : ℕ) : decide ((w : ℤ) = 0) = decide (w = 0) := by simp

private theorem loop_lc {rT : Type} (bounds : Val rT) (n m k : ℕ) (high : Bool) :
    (loop bounds n m k high).IsLocallyClosed := by
  unfold loop loopCode
  is_lc

private def loopValue {rT : Type} (bounds : Val rT) (n m k : ℕ) (high : Bool) : Val rT :=
  ⟨loop bounds n m k high, .fix (loop_lc bounds n m k high), loop_lc bounds n m k high⟩

@[simp, pl_step_simp] private theorem loop_openRec {rT : Type} (bounds : Val rT)
    (n m k : ℕ) (high : Bool) (d : ℕ) (e : Exp rT) :
    Exp.openRec d e (loop bounds n m k high) = loop bounds n m k high :=
  (Exp.open_lc d e _ (loop_lc bounds n m k high)).symm

private theorem body_lcb_of_loop {rT : Type} (body : Exp rT)
    (h : (Exp.fix (.lam (.lam body))).IsLocallyClosed) : Exp.lcb 3 body = true :=
  Exp.lc_imp_lcb h

private theorem loopBody_lcb {rT : Type} (bounds : Val rT) (n m k : ℕ) (high : Bool) :
    Exp.lcb 3 (loopBody bounds n m k high) = true :=
  body_lcb_of_loop _ (loop_lc bounds n m k high)

private def step {rT : Type} (bounds : Val rT) (n m k : ℕ) (high : Bool)
    (j : ℕ) (q : ℚ) : Exp rT :=
  stepCode (fun _ => (loopValue bounds n m k high).fst) (fun _ => bounds.fst)
    (fun _ => pl(#int (n : ℤ))) (fun _ => pl(#int (m : ℤ)))
    (fun _ => pl(#int (k : ℤ))) (fun _ => (Val.bool high).fst)
    (fun _ => pl(#int (m.choose k : ℤ))) (fun _ => pl(#int (j : ℤ)))
    (fun _ => (encode q).fst)

private theorem opened_loop {rT : Type} (bounds : Val rT) (n m k : ℕ) (high : Bool)
    (j : ℕ) (q : ℚ) :
    CurriedStep.opened [Val.int (j : ℤ), encode q]
      (Exp.openRec 2 (loop bounds n m k high) (loopBody bounds n m k high)) =
        step bounds n m k high j q := by
  rw [loopBody_eq]
  simp [CurriedStep.opened, step, stepCode, loopValue, Exp.openRec, openRec_val_fst,
    ClosedExp.openRec]

private theorem afterDenominator_lc {rT : Type} (bounds : Val rT) (n m k : ℕ)
    (high : Bool) : (Exp.lam (afterDenominator bounds n m k high)).IsLocallyClosed := by
  unfold afterDenominator loopCode start
  is_lc

private theorem opened_denominator {rT : Type} (bounds : Val rT) (n m k : ℕ) (high : Bool) :
    Exp.open' (afterDenominator bounds n m k high) (Val.int (m.choose k : ℤ)).fst =
      .app (.lam start) (loop bounds n m k high) := by
  simp [afterDenominator, loop, loopCode, start, Exp.open', Exp.openRec,
    openRec_val_fst, ClosedExp.openRec]

theorem conditional_lc {rT : Type} (bounds : Val rT) (n m k : ℕ) :
    (Exp.lam (highBody bounds n m k)).IsLocallyClosed := by
  unfold highBody bodyCode loopCode start
  is_lc

/-- The locally closed `high` closure, preserving arbitrary callback free variables. -/
def conditionalClosure {rT : Type} (bounds : Val rT) (n m k : ℕ) : Val rT :=
  ⟨.lam (highBody bounds n m k), .lam (conditional_lc bounds n m k),
    conditional_lc bounds n m k⟩

theorem opened_high {rT : Type} (bounds : Val rT) (n m k : ℕ) (high : Bool) :
    Exp.open' (highBody bounds n m k) (Val.bool high).fst =
      conditionalBody bounds n m k high := by
  simp [highBody, bodyCode, conditionalBody, afterDenominator, loopCode, start,
    Exp.open', Exp.openRec, openRec_val_fst, ClosedExp.openRec]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_chooseInt (E : CoPset) (n : ℕ) (k : ℤ) :
    ⊢ tglWp E pl(&Occil.FactoryExtra.choose #int (n : ℤ) #int k)
      (fun v : Val rT => iprop(⌜v = Val.int (chooseInt n k : ℤ)⌝)) := by
  by_cases hk : k < 0
  · twp_pures
    rw [negative_guard n k hk]
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp [chooseInt, hk]
  · have h := FactoryChoose.twp_choose (rT := rT) (GF := GF) E n k.toNat
    simpa only [chooseInt, hk, ite_false, Int.toNat_of_nonneg (by omega : 0 ≤ k)] using h

/-- The signed source subtraction contributes zero when the old count exceeds the new count. -/
theorem twp_choose_difference (E : CoPset) (n k j : ℕ) :
    ⊢ tglWp E pl(&Occil.FactoryExtra.choose #int (n : ℤ) #int ((k : ℤ) - j))
      (fun v : Val rT => iprop(⌜v = Val.int
        ((if j ≤ k then n.choose (k - j) else 0 : ℕ) : ℤ)⌝)) := by
  have h := twp_chooseInt (rT := rT) (GF := GF) E n ((k : ℤ) - j)
  by_cases hj : j ≤ k
  · have hnonneg : ¬(k : ℤ) - j < 0 := by omega
    simpa only [chooseInt, hnonneg, hj, ite_false, ite_true, Int.toNat_sub,
      Int.toNat_natCast] using h
  · have hneg : (k : ℤ) - j < 0 := by omega
    simpa only [chooseInt, hneg, hj, ite_true, ite_false] using h

private theorem loop_done (n j count : ℕ) (h : j + count = n + 1) (hc : count = 0) :
    decide ((n : ℤ) < j) = true := by simp; omega

private theorem loop_more (n j count : ℕ) (h : j + (count + 1) = n + 1) :
    decide ((n : ℤ) < j) = false := by simp; omega

private theorem twp_open_loop (E : CoPset) (bounds : Val rT) (n m k : ℕ) (high : Bool)
    (j : ℕ) (q : ℚ) (Φ : Val rT → IProp GF) :
    tglWp E (step bounds n m k high j q) Φ ⊢
      tglWp E pl(&(loop bounds n m k high) #int (j : ℤ) &(encode (rT := rT) q).fst) Φ := by
  have h := CurriedStep.twp_fix_apply (rT := rT) (GF := GF) E [] (Val.int (j : ℤ))
    [encode q] (loopBody bounds n m k high) (loopBody_lcb bounds n m k high) Φ
  change tglWp E (CurriedStep.opened [Val.int (j : ℤ), encode q]
      (Exp.openRec 2 (loop bounds n m k high) (loopBody bounds n m k high))) Φ ⊢
    tglWp E pl(&(loop bounds n m k high) #int (j : ℤ) &(encode (rT := rT) q).fst) Φ at h
  rwa [opened_loop] at h

private theorem twp_addCanonical (E : CoPset) (q r : ℚ) :
    ⊢ tglWp E pl(&Occil.FactoryExtra.addFraction &(encode (rT := rT) q).fst &(encode r).fst)
      (fun v : Val rT => iprop(⌜v = encode (q + r)⌝)) := by
  simpa only [Fraction.encode_ofRat, Fraction.value_ofRat] using
    twp_addFraction (rT := rT) (GF := GF) E (Fraction.ofRat q) (Fraction.ofRat r)

private theorem twp_select (E : CoPset) (lo hi : Fraction) (high : Bool) :
    ⊢ tglWp E (.cond (Val.bool high).fst (.snd (Val.pair lo.encode hi.encode).fst)
      (.fst (Val.pair lo.encode hi.encode).fst))
      (fun v : Val rT => iprop(⌜v = (if high then hi else lo).encode⌝)) := by
  cases high <;> twp_pures <;> twp_value <;> imodintro <;> ipureintro <;> apply Val.ext <;> rfl

private def weightFraction (n m k j : ℕ) (hkm : k ≤ m) : Fraction :=
  ⟨weight n m k j, m.choose k, Nat.choose_pos hkm⟩

private theorem weightFraction_value (n m k j : ℕ) (hkm : k ≤ m) :
    (weightFraction n m k j hkm).value = ReverseBinomial.coefficient n m k j := by
  simp only [weightFraction, Fraction.value, Rat.mkRat_eq_div, Rat.intCast_natCast]
  exact weight_coefficient n m k j

private theorem twp_loop (E : CoPset) (raw : ℕ → Bool → Fraction)
    (bounds : Val rT) (n m k : ℕ) (high : Bool) (hnm : n ≤ m) (hkm : k ≤ m)
    (hbound : ∀ j : ℕ, j ≤ n → ⊢ tglWp E pl(&bounds.fst #int (n : ℤ) #int (j : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.pair (raw j false).encode (raw j true).encode⌝)))
    (j count : ℕ) (hcount : j + count = n + 1) (q : ℚ) :
    ⊢ tglWp E pl(&(loop bounds n m k high) #int (j : ℤ) &(encode (rT := rT) q).fst)
      (fun v : Val rT => iprop(⌜v = encode (q + sumFrom raw n m k high j count)⌝)) := by
  induction count generalizing j q with
  | zero =>
    iapply twp_open_loop E bounds n m k high j q
    unfold step stepCode
    twp_pures
    rw [loop_done n j 0 hcount rfl]
    twp_pures
    twp_value
    imodintro
    ipureintro
    apply Val.ext
    simp [sumFrom]
  | succ count IH =>
    have hj : j ≤ n := by omega
    iapply twp_open_loop E bounds n m k high j q
    unfold step stepCode
    twp_pures
    rw [loop_more n j count hcount]
    twp_pure
    iterate 2 twp_pure
    rw [← Nat.cast_sub hnm]
    twp_bind pl(&Occil.FactoryExtra.choose #int ((m - n : ℕ) : ℤ) #int ((k : ℤ) - j))
    iapply tglWp_wand
    isplitl []
    · iapply twp_choose_difference E (m - n) k j
    iintro %v %hv
    subst v
    twp_bind pl(&Occil.FactoryExtra.choose #int (n : ℤ) #int (j : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply FactoryChoose.twp_choose E n j
    iintro %v %hv
    subst v
    iterate 2 twp_pure
    rw [weight_cast]
    simp only [ClosedExp.openRec]
    twp_pure
    simp only [beq_eq_decide, BaseLit.int.injEq]
    rw [zero_test (weight n m k j)]
    by_cases hw : weight n m k j = 0
    · rw [decide_eq_true hw]
      iterate 2 twp_pure
      rw [← Nat.cast_add_one]
      rw [sumFrom_succ, term_zero raw n m k j high hw, zero_add]
      have hrec := IH (j + 1) (by omega) q
      simp only [loopValue, Exp.ofVal]
      iapply hrec
    · rw [decide_eq_false hw]
      twp_pure
      twp_bind pl(&bounds.fst #int (n : ℤ) #int (j : ℤ))
      iapply tglWp_wand
      isplitl []
      · iapply hbound j hj
      iintro %v %hv
      subst v
      twp_pure
      twp_bind (.cond (Val.bool high).fst
        (.snd (Val.pair (raw j false).encode (raw j true).encode).fst)
        (.fst (Val.pair (raw j false).encode (raw j true).encode).fst))
      iapply tglWp_wand
      isplitl []
      · iapply twp_select E (raw j false) (raw j true) high
      iintro %v %hv
      subst v
      rw [selected]
      twp_pure
      simp only [ClosedExp.openRec]
      twp_bind pl(&Occil.FactoryExtra.multiplyFraction &(raw j high).encode.fst
        &(weightFraction n m k j hkm).encode.fst)
      iapply tglWp_wand
      isplitl []
      · iapply twp_multiplyFraction E (raw j high) (weightFraction n m k j hkm)
      iintro %v %hv
      subst v
      twp_pure
      simp only [ClosedExp.openRec]
      twp_bind pl(&Occil.FactoryExtra.addFraction &(encode (rT := rT) q).fst
        &(encode ((raw j high).value *
          (weightFraction n m k j hkm).value)).fst)
      iapply tglWp_wand
      isplitl []
      · iapply twp_addCanonical E q
          ((raw j high).value * (weightFraction n m k j hkm).value)
      iintro %v %hv
      subst v
      twp_pure
      rw [← Nat.cast_add_one]
      have hrec := IH (j + 1) (by omega) (q + term raw n m k high j)
      simp only [loopValue, Exp.ofVal]
      simp only [weightFraction_value]
      rw [sumFrom_succ, ← add_assoc]
      simp only [term] at hrec ⊢
      iapply hrec

/-- Compute the exact reverse-binomial average of one row of raw coefficients. -/
theorem twp_conditionalBody (E : CoPset) (raw : ℕ → Bool → Fraction)
    (bounds : Val rT) (n m k : ℕ) (high : Bool) (hnm : n ≤ m) (hkm : k ≤ m)
    (hbound : 0 < n → ∀ j : ℕ, j ≤ n →
      ⊢ tglWp E pl(&bounds.fst #int (n : ℤ) #int (j : ℤ))
        (fun v : Val rT => iprop(⌜v = Val.pair (raw j false).encode (raw j true).encode⌝))) :
    ⊢ tglWp E (conditionalBody bounds n m k high)
      (fun v : Val rT => iprop(⌜v = encode (mean raw n m k high)⌝)) := by
  unfold conditionalBody
  twp_pure
  simp only [beq_eq_decide, BaseLit.int.injEq]
  rw [zero_test n]
  by_cases hn : n = 0
  · rw [decide_eq_true hn]
    cases high <;> twp_pures <;> twp_value <;> imodintro <;> ipureintro <;>
      apply Val.ext <;> simp [mean, hn, encode]
  · rw [decide_eq_false hn]
    twp_pure
    twp_bind pl(&Occil.FactoryExtra.choose #int (m : ℤ) #int (k : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply FactoryChoose.twp_choose E m k
    iintro %v %hv
    subst v
    ieval (
      change _ ⊢ tglWp E
        (Ectx.fill ([] : Ectx rT) (.app (.lam (afterDenominator bounds n m k high))
          (Val.int (m.choose k : ℤ)).fst)) _)
    iapply (twp_beta E [] _ _ (afterDenominator_lc bounds n m k high) _)
    ieval (
      change _ ⊢ tglWp E
        (Exp.open' (afterDenominator bounds n m k high) (Val.int (m.choose k : ℤ)).fst) _)
    rw [opened_denominator]
    ieval (
      change _ ⊢ tglWp E
        (Ectx.fill ([] : Ectx rT) (.app (.lam start) (loopValue bounds n m k high).fst)) _)
    iapply (twp_beta E [] start (loopValue bounds n m k high) (by unfold start; is_lc) _)
    ieval (
      change _ ⊢ tglWp E
        pl(&(loop bounds n m k high) #0 &(encode (rT := rT) 0).fst) _)
    have h := twp_loop (rT := rT) (GF := GF) E raw bounds n m k high hnm hkm
      (hbound (by omega)) 0 (n + 1) (by omega) 0
    simp only [sumFrom, term, Nat.cast_zero, zero_add, mul_comm] at h
    simp only [mean, hn, ite_false]
    iapply h

/-- Invoke the source's conditional-average closure with either bound selector. -/
theorem twp_conditionalClosure (E : CoPset) (raw : ℕ → Bool → Fraction)
    (bounds : Val rT) (n m k : ℕ) (high : Bool) (hnm : n ≤ m) (hkm : k ≤ m)
    (hbound : 0 < n → ∀ j : ℕ, j ≤ n →
      ⊢ tglWp E pl(&bounds.fst #int (n : ℤ) #int (j : ℤ))
        (fun v : Val rT => iprop(⌜v = Val.pair (raw j false).encode (raw j true).encode⌝))) :
    ⊢ tglWp E pl(&(conditionalClosure bounds n m k).fst &(Val.bool high).fst)
      (fun v : Val rT => iprop(⌜v = encode (mean raw n m k high)⌝)) := by
  ieval (
    change _ ⊢ tglWp E
      (Ectx.fill ([] : Ectx rT) (.app (.lam (highBody bounds n m k)) (Val.bool high).fst)) _)
  iapply (twp_beta E [] _ _ (conditional_lc bounds n m k) _)
  ieval (
    change _ ⊢ tglWp E (Exp.open' (highBody bounds n m k) (Val.bool high).fst) _)
  rw [opened_high]
  iapply twp_conditionalBody E raw bounds n m k high hnm hkm hbound

end specification

end

end SampLib.EnvelopeConditionalAverage
