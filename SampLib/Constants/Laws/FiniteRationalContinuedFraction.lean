import SampLib.Uniform.Laws.RationalCoin
import SampLib.Bernoulli.Laws.CoinConditional

/-! # Finite rational continued-fraction coins

Backward evaluation defines the value of a finite coefficient prefix. A selector coin mixes
the terminal coin with the tail, and only a failed tail trial pays for the retry.
-/

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

/-- Credit amplification for one retry. -/
def factor (c : Coefficient) : ℝ≥0 := (retryBound c)⁻¹

theorem one_lt_factor (c : Coefficient) : 1 < factor c :=
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

end

end SampLib.FiniteRationalContinuedFraction
