import SampLib.Constants.Laws.RealContinuedFractionBudget
import SampLib.Uniform.Laws.RationalCoin
import SampLib.Bernoulli.Laws.CoinConditional

/-! # Rational continued-fraction coins

Rational coefficients embed into real continued fractions. A selector coin mixes the
terminal coin with the tail recursion, and a bounded potential funds both recursive calls.
-/

open ENNReal (ofReal)
open scoped ENNReal NNReal

namespace SampLib.RationalContinuedFraction

noncomputable section

/-- The source tuple represents `numerator/scale` over `denominator/scale`.
The lower bound one on each scaled numerator supplies uniform recursive progress. -/
structure Coefficient where
  numerator : ℕ
  denominator : ℕ
  scale : ℕ
  scale_pos : 0 < scale
  progress : scale ≤ numerator
  bounded : numerator ≤ denominator
  last : Bool

theorem Coefficient.positive (c : Coefficient) : 0 < c.numerator :=
  c.scale_pos.trans_le c.progress

theorem Coefficient.denominator_pos (c : Coefficient) : 0 < c.denominator :=
  c.positive.trans_le c.bounded

def Coefficient.real (c : Coefficient) : RealContinuedFraction.Coefficient where
  numerator := (c.numerator : ℝ) / c.scale
  denominator := (c.denominator : ℝ) / c.scale
  positive := div_pos (by exact_mod_cast c.positive) (by exact_mod_cast c.scale_pos)
  lower := (le_div_iff₀ (by exact_mod_cast c.scale_pos)).mpr (by
    simpa only [one_mul] using
      (show (c.scale : ℝ) ≤ c.denominator by exact_mod_cast c.progress.trans c.bounded))
  bounded := div_le_div_of_nonneg_right (by exact_mod_cast c.bounded) (by positivity)
  last := c.last

private def realDenominator (c : Coefficient) : ℝ≥0 :=
  ⟨c.real.denominator, c.real.denominator_pos.le⟩

abbrev sequence (a : ℕ → Coefficient) := fun i => (a i).real
def value (a : ℕ → Coefficient) := RealContinuedFraction.value (sequence a)
def potential (c : Coefficient) := RealContinuedFraction.potential c.real
abbrev one_le_potential (c : Coefficient) := RealContinuedFraction.one_le_potential c.real
abbrev potential_le_two (c : Coefficient) := RealContinuedFraction.potential_le_two c.real

private theorem value_coe (a : ℕ → Coefficient) (i : ℕ) :
    (value a i : ℝ) = (a i).numerator /
      ((a i).denominator + (a i).scale *
        (if (a i).last then 0 else (value a (i + 1) : ℝ))) := by
  unfold value
  rw [RealContinuedFraction.value_coe]
  have hd : ((a i).scale : ℝ) ≠ 0 := by exact_mod_cast (a i).scale_pos.ne'
  have ha : (0 : ℝ) < (a i).denominator := by exact_mod_cast (a i).denominator_pos
  have ht : 0 ≤ (if (a i).last then 0 else (value a (i + 1) : ℝ)) := by
    split_ifs <;> first | positivity | exact (value a (i + 1)).2.1
  have hden : (0 : ℝ) < (a i).denominator + (a i).scale *
      (if (a i).last then 0 else (value a (i + 1) : ℝ)) :=
    add_pos_of_pos_of_nonneg ha (mul_nonneg (by positivity) ht)
  simp only [value] at hden ⊢
  dsimp only [sequence, Coefficient.real]
  field_simp [hd, hden.ne']
  exact mul_div_cancel_right₀ _ hden.ne'

/-- The terminal coefficient coin. -/
def direct (c : Coefficient) : unitInterval :=
  RationalCoin.bias c.numerator c.denominator (by positivity)
    (by exact_mod_cast c.denominator_pos) (by exact_mod_cast c.bounded)

/-- The selector returns directly with probability `a/(a+d)`. -/
def selector (c : Coefficient) : unitInterval :=
  RationalCoin.bias c.denominator ((c.denominator : ℤ) + c.scale) (by positivity)
    (by have := c.denominator_pos; have := c.scale_pos; omega) (by omega)

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
  have htail : 0 < ((a i).denominator : ℝ) + (a i).scale * (value a (i + 1) : ℝ) :=
    add_pos_of_pos_of_nonneg ha (mul_nonneg (by positivity) (value a (i + 1)).2.1)
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
    ((1 / (realDenominator (a i) + 1 : ℝ≥0)) *
      ((4 / 3 : ℝ≥0) * potential (a (i + 1)) +
        NNReal.mk (1 - (value a (i + 1) : ℝ))
          (sub_nonneg.mpr (value a (i + 1)).2.2) *
          (4 / 3 : ℝ≥0) * potential (a i))) ≤ potential (a i) := by
  have h := RealContinuedFraction.recursive_budget (sequence a) i
    ((le_div_iff₀ (by exact_mod_cast (a (i + 1)).scale_pos)).mpr (by
      simpa only [one_mul] using
        (show ((a (i + 1)).scale : ℝ) ≤ (a (i + 1)).numerator by
          exact_mod_cast (a (i + 1)).progress)))
  rw [← NNReal.coe_le_coe]
  push_cast
  change 1 / ((a i).real.denominator + 1 : ℝ) *
    (4 / 3 * (potential (a (i + 1)) : ℝ) +
      (1 - (value a (i + 1) : ℝ)) * (4 / 3) * (potential (a i) : ℝ)) ≤ _
  dsimp only [value, potential, sequence] at h ⊢
  nlinarith

/-- The mixture preserves the fraction, while weighted slack funds both calls. -/
theorem expectation (a : ℕ → Coefficient) (i : ℕ) (hlast : (a i).last = false)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    RealCoin.credit (selector (a i)) (selectorCredit a i F ε) ≤
      RealCoin.credit (value a i) F + ε * potential (a i) := by
  have hs : ofReal (1 - (selector (a i) : ℝ)) =
      ((1 / (realDenominator (a i) + 1 : ℝ≥0)) : ℝ≥0∞) := by
    have ha : (0 : ℝ) < (a i).denominator := by exact_mod_cast (a i).denominator_pos
    have hd : (0 : ℝ) < (a i).scale := by exact_mod_cast (a i).scale_pos
    have h : 1 - (selector (a i) : ℝ) = 1 / ((a i).real.denominator + 1 : ℝ) := by
      dsimp [selector, RationalCoin.bias, Coefficient.real]
      push_cast
      field_simp
      ring
    rw [h]
    change ofReal (1 / ((realDenominator (a i) : ℝ) + 1)) = _
    have hcast : ofReal (((1 / (realDenominator (a i) + 1) : ℝ≥0) : ℝ)) =
        (((1 / (realDenominator (a i) + 1) : ℝ≥0) : ℝ≥0∞)) :=
      ENNReal.ofReal_coe_nnreal
    simpa only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_one,
      ENNReal.coe_div (by positivity : (realDenominator (a i) + 1 : ℝ≥0) ≠ 0),
      ENNReal.coe_one] using hcast
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
      ENNReal.coe_div (by positivity : (realDenominator (a i) + 1 : ℝ≥0) ≠ 0),
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

end SampLib.RationalContinuedFraction
