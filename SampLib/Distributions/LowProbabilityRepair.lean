import SampLib.Distributions.LowProbabilityMargin

/-! # Expectation preservation for the repaired low-probability factory -/

open ProbLang
open scoped ENNReal

namespace SampLib.LowProbabilityRepair

noncomputable section

structure Parameters (p : unitInterval) where
  a : ℤ
  b : ℤ
  m : ℤ
  n : ℤ
  admissible : LowProbabilityMargin.Admissible p a b m n

namespace Parameters

variable {p : unitInterval} (σ : Parameters p)

theorem n_pos : 0 < σ.n := by
  have := σ.admissible.2.2.1
  have := σ.admissible.2.2.2.1
  omega

theorem betaDen_pos : 0 < σ.n - 2 * σ.m := sub_pos.mpr σ.admissible.2.2.2.1

theorem betaDen_le : σ.n - 2 * σ.m ≤ σ.n := by
  have := σ.admissible.2.2.1
  omega

theorem m_pos (hm : σ.m ≠ 0) : 0 < σ.m :=
  lt_of_le_of_ne σ.admissible.2.2.1 (Ne.symm hm)

def bias : unitInterval :=
  LinearFactory.bias p σ.a σ.b 1 2 (LowProbabilityMargin.outer_admissible _ _ _ _ _ σ.admissible)

@[simp] theorem bias_coe : (σ.bias : ℝ) = Gambler.ratio p σ.a σ.b := rfl

theorem bias_zero (hm : σ.m = 0) : σ.bias = 0 := by
  apply Subtype.ext
  have hnonneg := σ.bias.2.1
  have hbound := σ.admissible.2.2.2.2
  simp only [hm, Int.cast_zero, zero_div] at hbound
  exact le_antisymm hbound hnonneg

theorem zero_expectation (hm : σ.m = 0) (F : Bool → ℝ≥0∞) :
    (∫⁻ z, F z ∂RealCoin.law σ.bias) = F false := by
  rw [σ.bias_zero hm]
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]

theorem contracting_expectation (hab : σ.a ≤ σ.b) (F : Bool → ℝ≥0∞) :
    (∫⁻ z, LinearFactory.contractingCredit p F z ∂RealCoin.law
      (RationalCoin.bias σ.a σ.b σ.admissible.1 σ.admissible.2.1 hab)) =
      ∫⁻ z, F z ∂RealCoin.law σ.bias := by
  simpa only [RealCoin.lintegral_law, bias, LinearFactory.bias] using
    LinearFactory.contracting_expectation
    (LinearFactory.Parameters.mk σ.a σ.b 1 2
      (LowProbabilityMargin.outer_admissible _ _ _ _ _ σ.admissible)) hab F

def innerBias (hm : 0 < σ.m) : unitInterval :=
  LinearFactory.bias p (σ.a * σ.n) (σ.b * 2 * σ.m) 1 2
    (LowProbabilityMargin.repaired_inner_admissible _ _ _ _ _ σ.admissible hm)

def selectorBias : unitInterval :=
  RationalCoin.bias (σ.n - 2 * σ.m) σ.n σ.betaDen_pos.le σ.n_pos σ.betaDen_le

def logisticBias (ha : σ.b < σ.a) : unitInterval :=
  LogisticFactory.integerBias p (σ.a * σ.n) (σ.b * (σ.n - 2 * σ.m))
    (mul_pos (σ.admissible.2.1.trans ha) σ.n_pos)
    (mul_pos σ.admissible.2.1 σ.betaDen_pos)

/-- The selector and linear branch cancel the logistic denominator. -/
theorem mixture_bias (ha : σ.b < σ.a) (hm : 0 < σ.m) :
    CoinConditional.bias (CoinConditional.bias 1 (σ.innerBias hm) σ.selectorBias)
      0 (σ.logisticBias ha) = σ.bias := by
  have hb : (σ.b : ℝ) ≠ 0 := by exact_mod_cast σ.admissible.2.1.ne'
  have hm' : (σ.m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn : (σ.n : ℝ) ≠ 0 := by exact_mod_cast σ.n_pos.ne'
  have hd : 0 < (σ.b : ℝ) * (σ.n - 2 * σ.m) + σ.a * σ.n * (p : ℝ) := by
    have hp : 0 ≤ (σ.a : ℝ) * σ.n * (p : ℝ) := by
      exact mul_nonneg (mul_nonneg (by exact_mod_cast σ.admissible.1)
        (by exact_mod_cast σ.n_pos.le)) p.2.1
    have hdiff : 0 < (σ.n : ℝ) - 2 * σ.m := by
      exact_mod_cast (sub_pos.mpr σ.admissible.2.2.2.1)
    exact add_pos_of_pos_of_nonneg
      (mul_pos (by exact_mod_cast σ.admissible.2.1) hdiff) hp
  apply Subtype.ext
  simp only [CoinConditional.bias, Set.Icc.convexComb, Set.Icc.coe_zero, Set.Icc.coe_one,
    bias, innerBias, selectorBias, logisticBias, LinearFactory.bias_coe,
    LogisticFactory.integerBias, RationalCoin.bias,
    Int.cast_mul, Int.cast_sub, Int.cast_ofNat]
  field_simp [hb, hm', hn, hd.ne']
  ring

end Parameters

def selectorCredit {p : unitInterval} (σ : Parameters p) (hm : 0 < σ.m)
    (F : Bool → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F true else ∫⁻ z, F z ∂RealCoin.law (σ.innerBias hm)

def firstCredit {p : unitInterval} (σ : Parameters p) (hm : 0 < σ.m)
    (F : Bool → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then ∫⁻ z, selectorCredit σ hm F z ∂RealCoin.law σ.selectorBias else F false

/-- Conditioning on the logistic and rational selectors preserves arbitrary credits. -/
theorem expectation {p : unitInterval} (σ : Parameters p) (ha : σ.b < σ.a)
    (hm : 0 < σ.m) (F : Bool → ℝ≥0∞) :
    (∫⁻ z, firstCredit σ hm F z ∂RealCoin.law (σ.logisticBias ha)) =
      ∫⁻ z, F z ∂RealCoin.law σ.bias := by
  have hinner : selectorCredit σ hm F =
      CoinConditional.firstCredit 1 (σ.innerBias hm) F := by
    funext b
    cases b <;> simp [selectorCredit, CoinConditional.firstCredit,
      RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]
  have houter : firstCredit σ hm F = CoinConditional.firstCredit
      (CoinConditional.bias 1 (σ.innerBias hm) σ.selectorBias) 0 F := by
    funext b
    cases b
    · simp [firstCredit, CoinConditional.firstCredit,
        RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]
    · change (∫⁻ z, selectorCredit σ hm F z ∂RealCoin.law σ.selectorBias) = _
      rw [hinner, CoinConditional.expectation_preservation]
      rfl
  rw [houter, CoinConditional.expectation_preservation]
  simp only [CoinConditional.law, σ.mixture_bias ha hm]

end

end SampLib.LowProbabilityRepair
