import SampLib.Constants.RationalContinuedFraction
import SampLib.Core.Syntax.ClosedExp
import Samplers.Constants.Exponential

/-! # Euler's continued-fraction coin, including its recursive tails -/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.EContinuedFraction

noncomputable section

def denominator (a j : ℕ) : ℕ :=
  if j = 0 then 1 else if j = 1 then a else if j % 3 = 0 then 2 * (j / 3) else 1

def scale (b j : ℕ) : ℕ := if j = 1 then b else 1

private theorem scale_pos (b j : ℕ) (hb : 0 < b) : 0 < scale b j := by
  unfold scale
  split_ifs <;> omega

private theorem scale_le (a b j : ℕ) (hab : b ≤ a) :
    scale b j ≤ denominator a j := by
  unfold scale denominator
  split_ifs <;> omega

/-- Position zero is an unreachable dummy coefficient; every source position is positive. -/
def coefficients (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) (j : ℕ) :
    RationalContinuedFraction.Coefficient where
  numerator := scale b j
  denominator := denominator a j
  scale := scale b j
  scale_pos := scale_pos b j hb
  progress := le_rfl
  bounded := scale_le a b j hab
  last := false

abbrev bias (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) (j : ℕ) : unitInterval :=
  RationalContinuedFraction.value (coefficients a b hb hab) j

private theorem guard (a b j : ℕ) (hb : 0 < b) (hab : b ≤ a) (hj : 0 < j) :
    ((decide ((b : ℤ) ≤ 0) || decide ((a : ℤ) < b)) || decide ((j : ℤ) ≤ 0)) = false := by
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
  omega

theorem eContinuedFraction_lc {rT : Type} :
    (Occil.Constants.eContinuedFraction : Exp rT).IsLocallyClosed := by is_lc

theorem eContinuedFraction_fv {rT : Type} :
    (Occil.Constants.eContinuedFraction : Exp rT).fv = ∅ := by
  simp [Occil.Constants.eContinuedFraction, Exp.fv, RationalCoin.rationalCoin_fv]

private instance eContinuedFraction_closed {rT : Type} :
    ClosedExp (Occil.Constants.eContinuedFraction : Exp rT) where
  lc := eContinuedFraction_lc
  fv := eContinuedFraction_fv

private def bodyWith {rT : Type} (a b j : ℕ) (d s : ℤ) : Exp rT := pl%
  if &Occil.rationalCoin #int d (#int d + #int s) then &Occil.rationalCoin #int s #int d
  else if &Occil.Constants.eContinuedFraction #int (a : ℤ) #int (b : ℤ)
      (#int (j : ℤ) + #1) then #false
    else &Occil.Constants.eContinuedFraction #int (a : ℤ) #int (b : ℤ) #int (j : ℤ)

private def body {rT : Type} (a b j : ℕ) : Exp rT :=
  bodyWith a b j (denominator a j) (scale b j)

private theorem one_test {rT : Type} [BEq rT] (j : ℕ) :
    ((BaseLit.int (j : ℤ) : BaseLit rT) == .int 1) = decide (j = 1) := by
  change decide ((j : ℤ) = 1) = decide (j = 1)
  exact decide_eq_decide.mpr (by omega)

private theorem mod_test {rT : Type} [BEq rT] (j : ℕ) :
    ((BaseLit.int ((j : ℤ) % 3) : BaseLit rT) == .int 0) = decide (j % 3 = 0) := by
  change decide ((j : ℤ) % 3 = 0) = decide (j % 3 = 0)
  exact decide_eq_decide.mpr (by omega)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec
  RationalCoin.rationalCoin_openRec RationalCoin.rationalCoin_closeRec

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_prepare (E : CoPset) (a b j : ℕ) (hb : 0 < b) (hab : b ≤ a)
    (hj : 0 < j) (Φ : Val rT → IProp GF) :
    tglWp E (body a b j) Φ ⊢
      tglWp E pl(&Occil.Constants.eContinuedFraction #int (a : ℤ) #int (b : ℤ)
        #int (j : ℤ)) Φ := by
  iintro Hbody
  iterate 4 twp_pure
  twp_pures
  rw [guard a b j hb hab hj]
  twp_pure
  by_cases h1 : j = 1
  · subst j
    iterate 6 twp_pure
    isimp only [body, denominator, scale, ite_false, ite_true, one_ne_zero] at Hbody
    ieval (change _ ⊢ tglWp E (bodyWith a b 1 (a : ℤ) (b : ℤ)) Φ)
    iexact Hbody
  · iterate 1 twp_pure
    rw [one_test, decide_eq_false h1]
    twp_pure
    by_cases h3 : j % 3 = 0
    · iterate 2 twp_pure
      rw [mod_test, decide_eq_true h3]
      iterate 5 twp_pure
      rw [one_test, decide_eq_false h1]
      iterate 2 twp_pure
      isimp only [body, denominator, scale, hj.ne', h1, h3, ite_false, ite_true,
        Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat,
        Int.natCast_ediv] at Hbody
      ieval (change _ ⊢ tglWp E (bodyWith a b j (2 * ((j : ℤ) / 3)) 1) Φ)
      iexact Hbody
    · iterate 2 twp_pure
      rw [mod_test, decide_eq_false h3]
      iterate 3 twp_pure
      rw [one_test, decide_eq_false h1]
      iterate 2 twp_pure
      isimp only [body, denominator, scale, hj.ne', h1, h3, ite_false, Nat.cast_one] at Hbody
      ieval (change _ ⊢ tglWp E (bodyWith a b j 1 1) Φ)
      iexact Hbody

private theorem direct_spec (E : CoPset) (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) (j : ℕ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.rationalCoin #int (scale b j : ℤ) #int (denominator a j : ℤ))
      (RealCoin.law (RationalContinuedFraction.direct (coefficients a b hb hab j))) Val.bool :=
  RationalCoin.rationalCoin_distSpec E _ _ (by positivity)
    (by exact_mod_cast (coefficients a b hb hab j).denominator_pos)
    (by exact_mod_cast (coefficients a b hb hab j).bounded)

private theorem selector_spec (E : CoPset) (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) (j : ℕ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.rationalCoin #int (denominator a j : ℤ)
        #int ((denominator a j : ℤ) + scale b j))
      (RealCoin.law (RationalContinuedFraction.selector (coefficients a b hb hab j))) Val.bool :=
  RationalCoin.rationalCoin_distSpec E _ _ (by positivity)
    (by have := (coefficients a b hb hab j).denominator_pos
        have := scale_pos b j hb
        omega) (by omega)

private theorem initial_budget (a b j : ℕ) (hb : 0 < b) (hab : b ≤ a) (δ : ℝ≥0∞) :
    δ / 2 * (RationalContinuedFraction.potential (coefficients a b hb hab j) : ℝ≥0∞) ≤ δ := by
  have ht : (RationalContinuedFraction.potential (coefficients a b hb hab j) : ℝ≥0∞) ≤ 2 := by
    exact_mod_cast RationalContinuedFraction.potential_le_two (coefficients a b hb hab j)
  calc
    _ ≤ δ / 2 * 2 := mul_le_mul_of_nonneg_left ht (by positivity)
    _ = δ := ENNReal.div_mul_cancel (by norm_num) (by norm_num)

set_option maxHeartbeats 800000 in
private theorem twp_weighted (E : CoPset) (a b : ℕ) (hb : 0 < b) (hab : b ≤ a)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ⊢ ∀ j : {j : ℕ // 0 < j},
      ↯ (ε * RationalContinuedFraction.potential (coefficients a b hb hab j.val)) -∗
      ∀ F : Bool → ℝ≥0∞, ↯ (RealCoin.credit (bias a b hb hab j.val) F) -∗
        tglWp E pl(&Occil.Constants.eContinuedFraction #int (a : ℤ) #int (b : ℤ)
          #int (j.val : ℤ))
          (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  let seq := coefficients a b hb hab
  iapply ErrorCredit.Induction.weighted
    (fun j : {j : ℕ // 0 < j} => RationalContinuedFraction.potential (seq j.val))
    (fun j => RationalContinuedFraction.one_le_potential (seq j.val)) _ ε hε (4 / 3)
    (by norm_num) $$ []
  iintro !> %ε %hε #IH %j Hterm %F Hcredit
  isimp only [ENNReal.coe_div (by norm_num : (3 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] at IH
  iapply twp_prepare E a b j.val hb hab j.property
  twp_pure
  twp_bind pl(&Occil.rationalCoin #int (denominator a j.val : ℤ)
    #int ((denominator a j.val : ℤ) + scale b j.val))
  icombine Hcredit Hterm as Htotal
  ihave Hsample := ErrorCredit.weaken
    (RationalContinuedFraction.expectation seq j.val rfl F ε) $$ Htotal
  isimp only [← RealCoin.lintegral_law] at Hsample
  iapply ((selector_spec E a b hb hab j.val).wp
    (RationalContinuedFraction.selectorCredit seq j.val F ε) (measurable_of_countable _) _)
    $$ Hsample
  iintro %selected Hcredit
  cases selected
  · twp_pure
    isimp only [RationalContinuedFraction.selectorCredit, Bool.false_eq_true, ite_false] at Hcredit
    ihave ⟨Htail, Hterm⟩ := ErrorCredit.split $$ Hcredit
    let next : {j : ℕ // 0 < j} := ⟨j.val + 1, Nat.succ_pos _⟩
    twp_bind pl(&Occil.Constants.eContinuedFraction #int (a : ℤ) #int (b : ℤ)
      (#int (j.val : ℤ) + #1))
    twp_pure
    rw [← Nat.cast_add_one]
    iapply tglWp_wand
    isplitl [Htail Hterm]
    · iapply IH $$ %next Hterm %(RationalContinuedFraction.tailCredit seq j.val F ε) Htail
    iintro %v ⟨%r, %hv, Hcredit⟩
    subst v
    cases r
    · twp_pure
      isimp only [RationalContinuedFraction.tailCredit, Bool.false_eq_true, ite_false] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      iapply IH $$ %j Hterm %F Hcredit
    · twp_pures
      twp_value
      imodintro
      iexists false
      isimp only [RationalContinuedFraction.tailCredit, ite_true] at Hcredit
      iframe Hcredit
      itrivial
  · twp_pure
    isimp only [RationalContinuedFraction.selectorCredit, ite_true,
      ← RealCoin.lintegral_law] at Hcredit
    iapply (direct_spec E a b hb hab j.val).spec F (measurable_of_countable _) $$ Hcredit

/-- A bounded state potential pays independently for both recursive calls. -/
theorem twp_eContinuedFraction (E : CoPset) (a b j : ℕ) (hb : 0 < b)
    (hab : b ≤ a) (hj : 0 < j) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias a b hb hab j) F) -∗
      tglWp E pl(&Occil.Constants.eContinuedFraction #int (a : ℤ) #int (b : ℤ) #int (j : ℤ))
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %δ %hδ Hterm
  have hε : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
  ihave Hterm := ErrorCredit.weaken (initial_budget a b j hb hab δ) $$ Hterm
  iapply twp_weighted E a b hb hab (δ / 2) hε $$ %⟨j, hj⟩ Hterm %F Hcredit

/-- Every positive source position samples its unique continued-fraction tail. -/
theorem eContinuedFraction_distSpec (E : CoPset) (a b j : ℕ) (hb : 0 < b)
    (hab : b ≤ a) (hj : 0 < j) :
    IsDistSpec (GF := GF) E
      pl(&Occil.Constants.eContinuedFraction #int (a : ℤ) #int (b : ℤ) #int (j : ℤ))
      (RealCoin.law (bias a b hb hab j)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_eContinuedFraction E a b j hb hab hj F)

end specification

end

end SampLib.EContinuedFraction
