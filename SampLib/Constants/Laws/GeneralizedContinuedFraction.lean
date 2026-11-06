import SampLib.Constants.Laws.ContinuedFraction
import SampLib.Uniform.Laws.RationalCoin
import SampLib.Bernoulli.Laws.CoinConditional

/-! # Integer continued-fraction coins

A selector coin mixes the terminal coin with the tail recursion. A bounded potential funds
both recursive calls.
-/

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

/-- A final coefficient is its own terminal coin. -/
theorem value_last (a : ℕ → Coefficient) (i : ℕ) (hlast : (a i).last = true) :
    value a i = direct (a i) := by
  apply Subtype.ext
  simp [value_coe, hlast, direct, RationalCoin.bias]

/-- Half the budget funds the first call, since the potential is at most two. -/
theorem initial_budget (c : Coefficient) (δ : ℝ≥0∞) :
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

/-- The start position is reachable. -/
theorem reachable_self (a : ℕ → Coefficient) (start : ℕ) : Reachable a start start :=
  ⟨le_rfl, by intro j hj hj'; omega⟩

/-- A nonfinal reachable position makes the next one reachable. -/
theorem reachable_next {a : ℕ → Coefficient} {start i : ℕ}
    (hi : Reachable a start i) (hlast : (a i).last = false) : Reachable a start (i + 1) := by
  refine ⟨hi.1.trans (Nat.le_succ _), ?_⟩
  intro j hj hj'
  by_cases hji : j < i
  · exact hi.2 j hj hji
  · have : j = i := by omega
    simpa [this] using hlast

end

end SampLib.ContinuedFraction
