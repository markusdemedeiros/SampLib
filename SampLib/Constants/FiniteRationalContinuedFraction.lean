import SampLib.Constants.RationalContinuedFraction
import SampLib.Uniform.RationalCoin
import SampLib.Bernoulli.CoinConditional
import Samplers.Constants.Engines

/-! # Finite positive rational continued fractions

Backward induction verifies the tail before the current position. The only
remaining recursion is a retry, whose probability is at most `d/(a+d) < 1`.
No lower bound on the scaled coefficients is required.
-/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.FiniteRationalContinuedFraction

noncomputable section

/-- The source tuple `(b,(a,(d,last)))`, representing `b/d` over `a/d`. -/
structure Coefficient where
  numerator : ℕ
  denominator : ℕ
  scale : ℕ
  positive : 0 < numerator
  bounded : numerator ≤ denominator
  scale_pos : 0 < scale
  last : Bool

theorem Coefficient.denominator_pos (c : Coefficient) : 0 < c.denominator :=
  c.positive.trans_le c.bounded

def direct (c : Coefficient) : unitInterval :=
  RationalCoin.bias c.numerator c.denominator (by positivity)
    (by exact_mod_cast c.denominator_pos) (by exact_mod_cast c.bounded)

def selector (c : Coefficient) : unitInterval :=
  RationalCoin.bias c.denominator ((c.denominator : ℤ) + c.scale) (by positivity)
    (by have := c.denominator_pos; have := c.scale_pos; omega) (by omega)

/-- The usual tail transformation `b/(a+d*x)`. -/
def step (c : Coefficient) (tail : unitInterval) : unitInterval :=
  ⟨(c.numerator : ℝ) / (c.denominator + c.scale * (tail : ℝ)),
    div_nonneg (by positivity)
      (add_nonneg (by positivity) (mul_nonneg (by positivity) tail.2.1)), by
    have ha : (0 : ℝ) < c.denominator := by exact_mod_cast c.denominator_pos
    have hden : 0 < (c.denominator : ℝ) + c.scale * (tail : ℝ) :=
      add_pos_of_pos_of_nonneg ha (mul_nonneg (by positivity) tail.2.1)
    apply (div_le_one hden).mpr
    have hb : (c.numerator : ℝ) ≤ c.denominator := by exact_mod_cast c.bounded
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ c.scale) tail.2.1]⟩

/-- Backward evaluation of a finite coefficient prefix, stopping at an earlier final flag. -/
def value (a : ℕ → Coefficient) : ℕ → ℕ → unitInterval
  | 0, i => direct (a i)
  | n + 1, i => if (a i).last then direct (a i) else step (a i) (value a n (i + 1))

private theorem mixture_value (c : Coefficient) (tail : unitInterval) :
    CoinConditional.bias (direct c)
      (CoinConditional.bias 0 (step c tail) tail) (selector c) = step c tail := by
  apply Subtype.ext
  have ha : (0 : ℝ) < c.denominator := by exact_mod_cast c.denominator_pos
  have hd : (0 : ℝ) < c.scale := by exact_mod_cast c.scale_pos
  have hden : 0 < (c.denominator : ℝ) + c.scale * (tail : ℝ) :=
    add_pos_of_pos_of_nonneg ha (mul_nonneg hd.le tail.2.1)
  change (1 - (selector c : ℝ)) *
    ((1 - (tail : ℝ)) * (step c tail : ℝ) + (tail : ℝ) * 0) +
    (selector c : ℝ) * (direct c : ℝ) = (step c tail : ℝ)
  dsimp [selector, direct, RationalCoin.bias, step]
  push_cast
  field_simp
  ring

private def retryBound (c : Coefficient) : ℝ≥0 :=
  ⟨1 - (selector c : ℝ), sub_nonneg.mpr (selector c).2.2⟩

private theorem retryBound_pos (c : Coefficient) : 0 < retryBound c := by
  change 0 < 1 - (selector c : ℝ)
  apply sub_pos.mpr
  have ha : (0 : ℝ) < c.denominator := by exact_mod_cast c.denominator_pos
  have hd : (0 : ℝ) < c.scale := by exact_mod_cast c.scale_pos
  dsimp [selector, RationalCoin.bias]
  push_cast
  apply (div_lt_one (by positivity : 0 < (c.denominator : ℝ) + c.scale)).mpr
  have h : (0 : ℝ) < c.scale := by exact_mod_cast c.scale_pos
  linarith

private theorem retryBound_lt_one (c : Coefficient) : retryBound c < 1 := by
  change 1 - (selector c : ℝ) < 1
  have ha : (0 : ℝ) < c.denominator := by exact_mod_cast c.denominator_pos
  have hd : (0 : ℝ) < c.scale := by exact_mod_cast c.scale_pos
  have h : 0 < (selector c : ℝ) := by
    dsimp [selector, RationalCoin.bias]
    push_cast
    positivity
  linarith

private def factor (c : Coefficient) : ℝ≥0 := (retryBound c)⁻¹

private theorem one_lt_factor (c : Coefficient) : 1 < factor c :=
  (one_lt_inv₀ (retryBound_pos c)).mpr (retryBound_lt_one c)

private theorem funded_retry (c : Coefficient) :
    ENNReal.ofReal (1 - (selector c : ℝ)) * (factor c : ℝ≥0∞) = 1 := by
  rw [ENNReal.ofReal_eq_coe_nnreal (sub_nonneg.mpr (selector c).2.2)]
  change (retryBound c : ℝ≥0∞) * ((retryBound c)⁻¹ : ℝ≥0) = 1
  rw [← ENNReal.coe_mul, mul_inv_cancel₀ (retryBound_pos c).ne', ENNReal.coe_one]

def tailCredit (c : Coefficient) (tail : unitInterval) (F : Bool → ℝ≥0∞)
    (ε : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F false else RealCoin.credit (step c tail) F + (factor c : ℝ≥0∞) * ε

def selectorCredit (c : Coefficient) (tail : unitInterval) (F : Bool → ℝ≥0∞)
    (ε : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then RealCoin.credit (direct c) F else RealCoin.credit tail (tailCredit c tail F ε)

/-- The tail recurrence preserves the fraction; its failure alone funds the next retry. -/
theorem expectation (c : Coefficient) (tail : unitInterval) (F : Bool → ℝ≥0∞)
    (ε : ℝ≥0∞) :
    RealCoin.credit (selector c) (selectorCredit c tail F ε) ≤
      RealCoin.credit (step c tail) F + ε := by
  have inner := CoinConditional.expectation_preservation 0 (step c tail) tail F
  have outer := CoinConditional.expectation_preservation (direct c)
    (CoinConditional.bias 0 (step c tail) tail) (selector c) F
  simp only [CoinConditional.law, CoinConditional.firstCredit,
    RealCoin.lintegral_law] at inner outer
  have hz : RealCoin.credit 0 F = F false := by simp [RealCoin.credit, RealCoin.pmf]
  simp only [hz] at inner
  rw [mixture_value c tail] at outer
  rw [← inner] at outer
  have hplain : RealCoin.credit (selector c) (selectorCredit c tail F 0) =
      RealCoin.credit (step c tail) F := by
    unfold selectorCredit tailCredit
    simpa only [mul_zero, add_zero] using outer
  have hsplit : RealCoin.credit (selector c) (selectorCredit c tail F ε) =
      RealCoin.credit (selector c) (selectorCredit c tail F 0) +
        (ENNReal.ofReal (1 - (selector c : ℝ)) * ENNReal.ofReal (1 - (tail : ℝ)) *
          (factor c : ℝ≥0∞)) * ε := by
    simp [RealCoin.credit, RealCoin.pmf, selectorCredit, tailCredit]
    ring
  rw [hsplit, hplain, mul_right_comm _ _ (factor c : ℝ≥0∞),
    funded_retry, one_mul]
  have hq : ENNReal.ofReal (1 - (tail : ℝ)) ≤ 1 :=
    ENNReal.ofReal_le_one.mpr (by linarith [tail.2.1])
  simpa only [one_mul, add_comm] using add_le_add_left
    (mul_le_mul_of_nonneg_right hq (show 0 ≤ ε by positivity)) (RealCoin.credit (step c tail) F)

/-- The concrete nested tuple returned by the coefficient oracle. -/
def encodeCoefficient {rT : Type} (c : Coefficient) : Val rT :=
  Val.pair (Val.int c.numerator)
    (Val.pair (Val.int c.denominator) (Val.pair (Val.int c.scale) (Val.bool c.last)))

private theorem valid_guard (c : Coefficient) :
    ((decide ((c.numerator : ℤ) ≤ 0) || decide ((c.denominator : ℤ) < c.numerator)) ||
      decide ((c.scale : ℤ) ≤ 0)) = false := by
  have hab : (c.numerator : ℤ) ≤ c.denominator := by exact_mod_cast c.bounded
  simp [c.positive.ne', c.scale_pos.ne', not_lt.mpr hab]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] RationalContinuedFraction.rationalContinuedFraction_openRec
  RationalContinuedFraction.rationalContinuedFraction_closeRec
  RationalCoin.rationalCoin_openRec RationalCoin.rationalCoin_closeRec

private theorem direct_spec (E : CoPset) (c : Coefficient) :
    IsDistSpec (GF := GF) E
      pl(&Occil.rationalCoin #int (c.numerator : ℤ) #int (c.denominator : ℤ))
      (RealCoin.law (direct c)) Val.bool :=
  RationalCoin.rationalCoin_distSpec E _ _ (by positivity)
    (by exact_mod_cast c.denominator_pos) (by exact_mod_cast c.bounded)

private theorem selector_spec (E : CoPset) (c : Coefficient) :
    IsDistSpec (GF := GF) E
      pl(&Occil.rationalCoin #int (c.denominator : ℤ)
        #int ((c.denominator : ℤ) + c.scale))
      (RealCoin.law (selector c)) Val.bool :=
  RationalCoin.rationalCoin_distSpec E _ _ (by positivity)
    (by have := c.denominator_pos; have := c.scale_pos; omega) (by omega)

set_option maxHeartbeats 600000 in
private theorem twp_terminal (E : CoPset) (c : Coefficient) (position : ℕ)
    (coefficient : Val rT) (hlast : c.last = true)
    (hentry : ⊢ tglWp E pl(&coefficient.fst #int (position : ℤ))
      (fun v : Val rT => iprop(⌜v = encodeCoefficient c⌝))) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (direct c) F) -∗
      tglWp E pl(&Occil.Constants.rationalContinuedFraction &coefficient.fst #int (position : ℤ))
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iterate 3 twp_pure
  twp_bind pl(&coefficient.fst #int (position : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply hentry
  iintro %v %hv
  subst v
  twp_pures
  rw [valid_guard c]
  twp_pure
  rw [hlast]
  twp_pure
  isimp only [← RealCoin.lintegral_law] at Hcredit
  iapply (direct_spec E c).spec F (measurable_of_countable _) $$ Hcredit

set_option maxHeartbeats 1600000 in
private theorem twp_nonterminal (E : CoPset) (c : Coefficient) (position : ℕ)
    (coefficient : Val rT) (hlast : c.last = false)
    (hentry : ⊢ tglWp E pl(&coefficient.fst #int (position : ℤ))
      (fun v : Val rT => iprop(⌜v = encodeCoefficient c⌝)))
    (tail : unitInterval)
    (htail : IsDistSpec (GF := GF) E
      pl(&Occil.Constants.rationalContinuedFraction &coefficient.fst #int ((position + 1 : ℕ) : ℤ))
      (RealCoin.law tail) Val.bool) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (step c tail) F) -∗
      tglWp E pl(&Occil.Constants.rationalContinuedFraction &coefficient.fst #int (position : ℤ))
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert %F Hcredit
  iapply ErrorCredit.Induction.simple hε (one_lt_factor c) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ %F Hcredit
  iterate 3 twp_pure
  twp_bind pl(&coefficient.fst #int (position : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply hentry
  iintro %v %hv
  subst v
  twp_pures
  rw [valid_guard c]
  twp_pure
  rw [hlast]
  iterate 2 twp_pure
  twp_bind pl(&Occil.rationalCoin #int (c.denominator : ℤ)
    #int ((c.denominator : ℤ) + c.scale))
  icombine Hcredit Hterm as Htotal
  ihave Hsample := ErrorCredit.weaken (expectation c tail F ε) $$ Htotal
  isimp only [← RealCoin.lintegral_law] at Hsample
  iapply ((selector_spec E c).wp (selectorCredit c tail F ε)
    (measurable_of_countable _) _) $$ Hsample
  iintro %selected Hcredit
  cases selected
  · iterate 2 twp_pure
    isimp only [selectorCredit, Bool.false_eq_true, ite_false] at Hcredit
    twp_bind pl(&Occil.Constants.rationalContinuedFraction &coefficient.fst
      #int ((position : ℤ) + 1))
    rw [← Nat.cast_add_one]
    isimp only [← RealCoin.lintegral_law] at Hcredit
    iapply (htail.wp (tailCredit c tail F ε) (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    cases b
    · twp_pure
      isimp only [tailCredit, Bool.false_eq_true, ite_false] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      ieval (
        change _ ⊢ tglWp E
          pl(&Occil.Constants.rationalContinuedFraction &coefficient.fst #int (position : ℤ)) _)
      iapply IH $$ Hterm %F Hcredit
    · twp_pures
      twp_value
      imodintro
      iexists false
      isimp only [tailCredit, ite_true] at Hcredit
      iframe Hcredit
      itrivial
  · twp_pure
    isimp only [selectorCredit, ite_true, ← RealCoin.lintegral_law] at Hcredit
    iapply (direct_spec E c).spec F (measurable_of_countable _) $$ Hcredit

/-- Finite prefixes require only the guards actually checked by the source. -/
theorem twp_rationalContinuedFraction_finite (E : CoPset) (a : ℕ → Coefficient)
    (coefficient : Val rT) (depth start : ℕ) (hfinal : (a (start + depth)).last = true)
    (horacle : ∀ i, start ≤ i → i ≤ start + depth →
      ⊢ tglWp E pl(&coefficient.fst #int (i : ℤ))
        (fun v : Val rT => iprop(⌜v = encodeCoefficient (a i)⌝)))
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (value a depth start) F) -∗
      tglWp E pl(&Occil.Constants.rationalContinuedFraction &coefficient.fst #int (start : ℤ))
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  induction depth generalizing start F with
  | zero =>
    simpa only [value] using twp_terminal E (a start) start coefficient
      (by simpa using hfinal) (horacle start le_rfl (by omega)) F
  | succ depth IH =>
    cases hlast : (a start).last
    · have htail : IsDistSpec (GF := GF) E
        pl(&Occil.Constants.rationalContinuedFraction &coefficient.fst
          #int ((start + 1 : ℕ) : ℤ)) (RealCoin.law (value a depth (start + 1))) Val.bool := by
        refine ⟨fun G _ => ?_⟩
        simpa only [RealCoin.lintegral_law] using wand_entails
          (IH (start + 1) (by simpa [Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hfinal) (fun i hlo hhi => horacle i (by omega) (by omega)) G)
      simpa only [value, hlast, Bool.false_eq_true, ite_false] using
        twp_nonterminal E (a start) start coefficient hlast
          (horacle start le_rfl (by omega)) (value a depth (start + 1)) htail F
    · simpa only [value, hlast, ite_true] using
        twp_terminal E (a start) start coefficient hlast (horacle start le_rfl (by omega)) F

/-- The finite rational fraction, with arbitrary positive rational coefficient sizes. -/
theorem rationalContinuedFraction_finite_distSpec (E : CoPset) (a : ℕ → Coefficient)
    (coefficient : Val rT) (depth start : ℕ) (hfinal : (a (start + depth)).last = true)
    (horacle : ∀ i, start ≤ i → i ≤ start + depth →
      ⊢ tglWp E pl(&coefficient.fst #int (i : ℤ))
        (fun v : Val rT => iprop(⌜v = encodeCoefficient (a i)⌝))) :
    IsDistSpec (GF := GF) E
      pl(&Occil.Constants.rationalContinuedFraction &coefficient.fst #int (start : ℤ))
      (RealCoin.law (value a depth start)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using wand_entails
      (twp_rationalContinuedFraction_finite E a coefficient depth start hfinal horacle F)

end specification

end

end SampLib.FiniteRationalContinuedFraction
