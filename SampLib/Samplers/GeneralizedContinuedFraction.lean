import SampLib.Distributions.ContinuedFraction
import SampLib.Samplers.RationalCoin
import SampLib.Samplers.CoinConditional
import SampLib.WeightedAmplification
import Samplers.Constants.Engines

/-! # Positive integer generalized continued fractions

The canonical fraction is determined by its finite prefixes. The recursion may
call both the tail and itself; a bounded state potential pays each call separately.
-/

open ProbLang
open ENNReal (ofReal)
open scoped ENNReal NNReal

namespace SampLib.ContinuedFraction

noncomputable section

/-- The terminal coefficient coin. -/
def direct (c : Coefficient) : unitInterval :=
  RationalCoin.bias c.numerator c.denominator (by positivity)
    (by exact_mod_cast c.denominator_pos) (by exact_mod_cast c.bounded)

/-- The selector returns directly with probability `a/(a+1)`. -/
def selector (c : Coefficient) : unitInterval :=
  RationalCoin.bias c.denominator ((c.denominator : ℤ) + 1) (by positivity)
    (by have := c.denominator_pos; omega) (by omega)

private theorem mixture_value (a : ℕ → Coefficient) (i : ℕ) (hlast : (a i).last = false) :
    CoinConditional.bias (direct (a i))
      (CoinConditional.bias 0 (value a i) (value a (i + 1))) (selector (a i)) = value a i := by
  apply Subtype.ext
  have ha : (0 : ℝ) < (a i).denominator := by exact_mod_cast (a i).denominator_pos
  have hp := value_coe a i
  simp only [hlast, Bool.false_eq_true, ite_false] at hp
  change (1 - (selector (a i) : ℝ)) *
    ((1 - (value a (i + 1) : ℝ)) * (value a i : ℝ) + (value a (i + 1) : ℝ) * 0) +
    (selector (a i) : ℝ) * (direct (a i) : ℝ) = (value a i : ℝ)
  dsimp [selector, direct, RationalCoin.bias]
  push_cast
  have htail : 0 < ((a i).denominator : ℝ) + (value a (i + 1) : ℝ) :=
    add_pos_of_pos_of_nonneg ha (value a (i + 1)).2.1
  rw [hp]
  field_simp
  ring

private theorem value_last (a : ℕ → Coefficient) (i : ℕ) (hlast : (a i).last = true) :
    value a i = direct (a i) := by
  apply Subtype.ext
  simp [value_coe, hlast, direct, RationalCoin.bias]

private theorem initial_budget (c : Coefficient) (δ : ℝ≥0∞) :
    δ / 2 * (potential c : ℝ≥0∞) ≤ δ := by
  have ht : (potential c : ℝ≥0∞) ≤ 2 := by exact_mod_cast potential_le_two c
  calc
    _ ≤ δ / 2 * 2 := mul_le_mul_of_nonneg_left ht (by positivity)
    _ = δ := ENNReal.div_mul_cancel (by norm_num) (by norm_num)

/-- Continuation after the tail coin: success stops with false; failure retries. -/
def tailCredit (a : ℕ → Coefficient) (i : ℕ) (F : Bool → ℝ≥0∞)
    (ε : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F false else RealCoin.credit (value a i) F + (4 / 3 : ℝ≥0∞) * ε * potential (a i)

/-- Continuation after the selector, including the separately funded tail call. -/
def selectorCredit (a : ℕ → Coefficient) (i : ℕ) (F : Bool → ℝ≥0∞)
    (ε : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then RealCoin.credit (direct (a i)) F
  else RealCoin.credit (value a (i + 1)) (tailCredit a i F ε) +
    (4 / 3 : ℝ≥0∞) * ε * potential (a (i + 1))

private theorem plain_expectation (a : ℕ → Coefficient) (i : ℕ)
    (hlast : (a i).last = false) (F : Bool → ℝ≥0∞) :
    RealCoin.credit (selector (a i)) (selectorCredit a i F 0) =
      RealCoin.credit (value a i) F := by
  have inner := CoinConditional.expectation_preservation 0 (value a i) (value a (i + 1)) F
  have outer := CoinConditional.expectation_preservation (direct (a i))
    (CoinConditional.bias 0 (value a i) (value a (i + 1))) (selector (a i)) F
  simp only [CoinConditional.law, CoinConditional.firstCredit,
    RealCoin.lintegral_law] at inner outer
  have hz : RealCoin.credit 0 F = F false := by simp [RealCoin.credit, RealCoin.pmf]
  simp only [hz] at inner
  rw [mixture_value a i hlast] at outer
  rw [← inner] at outer
  unfold selectorCredit tailCredit
  simpa only [mul_zero, zero_mul, add_zero] using outer

private theorem weighted_budget (a : ℕ → Coefficient) (i : ℕ) :
    ((1 / ((a i).denominator + 1 : ℝ≥0)) *
      ((4 / 3 : ℝ≥0) * potential (a (i + 1)) +
        NNReal.mk (1 - (value a (i + 1) : ℝ))
          (sub_nonneg.mpr (value a (i + 1)).2.2) *
          (4 / 3 : ℝ≥0) * potential (a i))) ≤ potential (a i) := by
  have h := recursive_budget a i
  rw [← NNReal.coe_le_coe]
  push_cast
  change 1 / ((a i).denominator + 1 : ℝ) *
    (4 / 3 * (potential (a (i + 1)) : ℝ) +
      (1 - (value a (i + 1) : ℝ)) * (4 / 3) * (potential (a i) : ℝ)) ≤ _
  nlinarith

/-- The mixture preserves the fraction, while weighted slack funds both calls. -/
theorem expectation (a : ℕ → Coefficient) (i : ℕ) (hlast : (a i).last = false)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    RealCoin.credit (selector (a i)) (selectorCredit a i F ε) ≤
      RealCoin.credit (value a i) F + ε * potential (a i) := by
  have hs : ofReal (1 - (selector (a i) : ℝ)) =
      ((1 / ((a i).denominator + 1 : ℝ≥0)) : ℝ≥0∞) := by
    have ha : (0 : ℝ) < (a i).denominator := by exact_mod_cast (a i).denominator_pos
    have h : 1 - (selector (a i) : ℝ) = 1 / ((a i).denominator + 1 : ℝ) := by
      dsimp [selector, RationalCoin.bias]
      push_cast
      field_simp
      ring
    rw [h]
    rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < (a i).denominator + 1)]
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    simp
  have hb := weighted_budget a i
  have hb' :
      ofReal (1 - (selector (a i) : ℝ)) *
        ((4 / 3 : ℝ≥0∞) * potential (a (i + 1)) +
          ofReal (1 - (value a (i + 1) : ℝ)) * (4 / 3 : ℝ≥0∞) * potential (a i)) ≤
        potential (a i) := by
    rw [hs]
    rw [ENNReal.ofReal_eq_coe_nnreal (sub_nonneg.mpr (value a (i + 1)).2.2)]
    have hbcast := ENNReal.coe_le_coe.mpr hb
    simp only [ENNReal.coe_mul, ENNReal.coe_add,
      ENNReal.coe_div (by norm_num : (3 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by positivity : ((a i).denominator + 1 : ℝ≥0) ≠ 0),
      ENNReal.coe_one, ENNReal.coe_ofNat] at hbcast
    convert hbcast using 1
    congr 2
  have hsplit :
      RealCoin.credit (selector (a i)) (selectorCredit a i F ε) =
        RealCoin.credit (selector (a i)) (selectorCredit a i F 0) +
          (ofReal (1 - (selector (a i) : ℝ)) *
            ((4 / 3 : ℝ≥0∞) * potential (a (i + 1)) +
              ofReal (1 - (value a (i + 1) : ℝ)) * (4 / 3 : ℝ≥0∞) * potential (a i))) * ε := by
    simp [RealCoin.credit, RealCoin.pmf, selectorCredit, tailCredit]
    ring
  rw [hsplit, plain_expectation a i hlast]
  exact add_le_add le_rfl
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right hb' (by positivity : 0 ≤ ε))

/-- Exactly the coefficient positions reachable before the first final flag. -/
def Reachable (a : ℕ → Coefficient) (start i : ℕ) : Prop :=
  start ≤ i ∧ ∀ j, start ≤ j → j < i → (a j).last = false

private theorem reachable_self (a : ℕ → Coefficient) (start : ℕ) : Reachable a start start :=
  ⟨le_rfl, by intro j hj hj'; omega⟩

private theorem reachable_next {a : ℕ → Coefficient} {start i : ℕ}
    (hi : Reachable a start i) (hlast : (a i).last = false) : Reachable a start (i + 1) := by
  refine ⟨hi.1.trans (Nat.le_succ _), ?_⟩
  intro j hj hj'
  by_cases hji : j < i
  · exact hi.2 j hj hji
  · have : j = i := by omega
    simpa [this] using hlast

/-- The callback representation `(b,(a,last))`. -/
def encodeCoefficient {rT : Type _} (c : Coefficient) : Val rT :=
  Val.pair (Val.int c.numerator) (Val.pair (Val.int c.denominator) (Val.bool c.last))

private theorem valid_guard (c : Coefficient) :
    (decide ((c.numerator : ℤ) ≤ 0) || decide ((c.denominator : ℤ) < c.numerator)) = false := by
  have hab : (c.numerator : ℤ) ≤ c.denominator := by exact_mod_cast c.bounded
  simp [c.positive.ne', not_lt.mpr hab]

theorem generalizedContinuedFraction_lc {rT : Type _} :
    (Occil.Constants.generalizedContinuedFraction : Exp rT).IsLocallyClosed := by is_lc

theorem generalizedContinuedFraction_fv {rT : Type _} :
    (Occil.Constants.generalizedContinuedFraction : Exp rT).fv = ∅ := by
  simp [Occil.Constants.generalizedContinuedFraction, Exp.fv, RationalCoin.rationalCoin_fv]

@[simp] theorem generalizedContinuedFraction_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.Constants.generalizedContinuedFraction =
      Occil.Constants.generalizedContinuedFraction :=
  (Exp.open_lc k e _ generalizedContinuedFraction_lc).symm

@[simp] theorem generalizedContinuedFraction_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.Constants.generalizedContinuedFraction : Exp rT) =
      Occil.Constants.generalizedContinuedFraction :=
  Exp.closeRec_fresh x _ k (by simp [generalizedContinuedFraction_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem direct_distSpec (E : CoPset) (c : Coefficient) :
    IsDistSpec (GF := GF) E pl(&Occil.rationalCoin #int (c.numerator : ℤ)
      #int (c.denominator : ℤ)) (RealCoin.law (direct c)) Val.bool :=
  RationalCoin.rationalCoin_distSpec E _ _ (by positivity)
    (by exact_mod_cast c.denominator_pos) (by exact_mod_cast c.bounded)

private theorem selector_distSpec (E : CoPset) (c : Coefficient) :
    IsDistSpec (GF := GF) E pl(&Occil.rationalCoin #int (c.denominator : ℤ)
      #int ((c.denominator : ℤ) + 1)) (RealCoin.law (selector c)) Val.bool :=
  RationalCoin.rationalCoin_distSpec E _ _ (by positivity)
    (by have := c.denominator_pos; omega) (by omega)

set_option maxHeartbeats 600000 in
private theorem twp_weighted (E : CoPset) (a : ℕ → Coefficient) (start : ℕ)
    (coefficient : Val rT)
    (hcoefficient : ∀ i, Reachable a start i →
      ⊢ tglWp E pl(&coefficient.fst #int (i : ℤ))
        (fun v : Val rT => iprop(⌜v = encodeCoefficient (a i)⌝)))
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ⊢ ∀ i : {i // Reachable a start i}, ↯ (ε * potential (a i.val)) -∗
      ∀ F : Bool → ℝ≥0∞, ↯ (RealCoin.credit (value a i.val) F) -∗
        tglWp E pl(&Occil.Constants.generalizedContinuedFraction &coefficient.fst #int (i.val : ℤ))
          (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iapply ErrorCredit.Induction.weighted
    (fun i : {i // Reachable a start i} => potential (a i.val))
    (fun i => one_le_potential (a i.val)) _ ε hε (4 / 3) (by norm_num) $$ []
  iintro !> %ε %hε #IH %i Hterm %F Hcredit
  isimp only [ENNReal.coe_div (by norm_num : (3 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] at IH
  iterate 3 twp_pure
  twp_bind pl(&coefficient.fst #int (i.val : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply hcoefficient i.val i.property
  iintro %v %hv
  subst v
  twp_pures
  rw [valid_guard (a i.val)]
  twp_pure
  simp only [RationalCoin.rationalCoin_closeRec, RationalCoin.rationalCoin_openRec]
  cases hlast : (a i.val).last
  · iterate 2 twp_pure
    twp_bind pl(&Occil.rationalCoin #int ((a i.val).denominator : ℤ)
      #int ((a i.val).denominator + 1 : ℤ))
    icombine Hcredit Hterm as Htotal
    ihave Hsample := ErrorCredit.weaken (expectation a i.val hlast F ε) $$ Htotal
    isimp only [← RealCoin.lintegral_law] at Hsample
    iapply ((selector_distSpec E (a i.val)).wp
      (selectorCredit a i.val F ε) (measurable_of_countable _) _) $$ Hsample
    iintro %selected Hcredit
    cases selected
    · iterate 2 twp_pure
      isimp only [selectorCredit, Bool.false_eq_true, ite_false] at Hcredit
      ihave ⟨Htail, Hterm⟩ := ErrorCredit.split $$ Hcredit
      let inext : {j // Reachable a start j} :=
        ⟨i.val + 1, reachable_next i.property hlast⟩
      twp_bind pl(&Occil.Constants.generalizedContinuedFraction &coefficient.fst
        #int ((i.val : ℤ) + 1))
      rw [← Nat.cast_add_one]
      iapply tglWp_wand
      isplitl [Htail Hterm]
      · iapply IH $$ %inext Hterm %(tailCredit a i.val F ε) Htail
      iintro %v ⟨%b, %hv, Hcredit⟩
      subst v
      cases b
      · twp_pure
        isimp only [tailCredit, Bool.false_eq_true, ite_false] at Hcredit
        ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
        ieval (
          change _ ⊢ tglWp E
            pl(&Occil.Constants.generalizedContinuedFraction &coefficient.fst #int (i.val : ℤ)) _)
        iapply IH $$ %i Hterm %F Hcredit
      · twp_pures
        twp_value
        imodintro
        iexists false
        isimp only [tailCredit, ite_true] at Hcredit
        iframe Hcredit
        itrivial
    · twp_pure
      isimp only [selectorCredit, ite_true] at Hcredit
      isimp only [← RealCoin.lintegral_law] at Hcredit
      iapply (direct_distSpec E (a i.val)).spec F (measurable_of_countable _) $$ Hcredit
  · twp_pure
    isimp only [value_last a i.val hlast, ← RealCoin.lintegral_law] at Hcredit
    iapply (direct_distSpec E (a i.val)).spec F (measurable_of_countable _) $$ Hcredit

/-- CTE sampling of the canonical fraction. Only reachable coefficients are queried. -/
theorem twp_generalizedContinuedFraction (E : CoPset) (a : ℕ → Coefficient) (start : ℕ)
    (coefficient : Val rT)
    (hcoefficient : ∀ i, Reachable a start i →
      ⊢ tglWp E pl(&coefficient.fst #int (i : ℤ))
        (fun v : Val rT => iprop(⌜v = encodeCoefficient (a i)⌝)))
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (value a start) F) -∗
      tglWp E pl(&Occil.Constants.generalizedContinuedFraction &coefficient.fst #int (start : ℤ))
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %δ %hδ Hterm
  have hε : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
  ihave Hterm := ErrorCredit.weaken (initial_budget (a start) δ) $$ Hterm
  iapply twp_weighted E a start coefficient hcoefficient (δ / 2) hε $$
    %⟨start, reachable_self a start⟩ Hterm %F Hcredit

/-- Bernoulli at the unique value of all finite continued-fraction prefixes. -/
theorem generalizedContinuedFraction_distSpec (E : CoPset) (a : ℕ → Coefficient) (start : ℕ)
    (coefficient : Val rT)
    (hcoefficient : ∀ i, Reachable a start i →
      ⊢ tglWp E pl(&coefficient.fst #int (i : ℤ))
        (fun v : Val rT => iprop(⌜v = encodeCoefficient (a i)⌝))) :
    IsDistSpec (GF := GF) E
      pl(&Occil.Constants.generalizedContinuedFraction &coefficient.fst #int (start : ℤ))
      (RealCoin.law (value a start)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_generalizedContinuedFraction E a start coefficient hcoefficient F)

end specification

end

end SampLib.ContinuedFraction
