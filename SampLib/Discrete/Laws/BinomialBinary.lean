import SampLib.Discrete.Laws.BinomialThinning
import SampLib.Common.Laws.Urn
import SampLib.Bernoulli.VonNeumann

/-! # Binary refinement of a binomial bias

Each fair split either retains the selected trials or fills the unselected
trials. Independent thinning and its complement identify both conditional laws.
The expected number of unresolved trials is halved at every refinement.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace SampLib.BinomialBinary

noncomputable section

/-- Rational success bias, with a harmless total extension outside the input domain. -/
def bias (a b : ℕ) : unitInterval := Urn.bias a (b - a)

abbrev law (n a b : ℕ) := Binomial.law (bias a b) n

/-- Valid natural parameters denote their exact rational bias. -/
theorem bias_coe (a b : ℕ) (hb : 0 < b) (hab : a ≤ b) :
    (bias a b : ℝ) = a / b := by
  have h : a + (b - a) = b := by omega
  simp only [bias, Urn.bias, h, hb, dite_true, RationalCoin.bias]
  rw [← Nat.cast_add, h]
  simp

@[simp] theorem bias_zero (b : ℕ) : bias 0 b = 0 := by
  apply Subtype.ext
  by_cases hb : 0 < b
  · simp [bias_coe 0 b hb (Nat.zero_le b)]
  · simp [bias, Urn.bias, show b = 0 by omega]

@[simp] theorem bias_full (b : ℕ) (hb : 0 < b) : bias b b = 1 := by
  apply Subtype.ext
  simp [bias_coe b b hb le_rfl, Nat.ne_of_gt hb]

/-- Either stopping condition leaves no unresolved successes. -/
theorem expectation_stop (n a b successes : ℕ) (F : ℕ → ℝ≥0∞)
    (h : n = 0 ∨ a = 0) :
    (∫⁻ k, F (successes + k) ∂law n a b) = F successes := by
  rcases h with rfl | rfl <;> simp [law, Binomial.expectation_zero]

private theorem low_bias (a b : ℕ) (hb : 0 < b) (h : 2 * a < b) :
    VonNeumann.fairBias * bias (2 * a) b = bias a b := by
  apply Subtype.ext
  change (1 / 2 : ℝ) * (bias (2 * a) b : ℝ) = (bias a b : ℝ)
  rw [bias_coe (2 * a) b hb (by omega), bias_coe a b hb (by omega)]
  push_cast
  ring

private theorem high_bias (a b : ℕ) (hb : 0 < b) (ha : a < b) (h : b ≤ 2 * a) :
    unitInterval.symm (unitInterval.symm VonNeumann.fairBias *
      unitInterval.symm (bias (2 * a - b) b)) = bias a b := by
  apply Subtype.ext
  change 1 - (1 - (1 / 2 : ℝ)) * (1 - (bias (2 * a - b) b : ℝ)) =
    (bias a b : ℝ)
  rw [bias_coe (2 * a - b) b hb (by omega), bias_coe a b hb (by omega)]
  rw [Nat.cast_sub h]
  push_cast
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  field_simp
  ring

/-- The exact expected continuation after a binary refinement. -/
theorem expectation (n a b successes : ℕ) (hb : 0 < b) (ha : a < b)
    (F : ℕ → ℝ≥0∞) :
    (∫⁻ half,
      (if b ≤ 2 * a then
        ∫⁻ k, F (successes + half + k) ∂law (n - half) (2 * a - b) b
      else ∫⁻ k, F (successes + k) ∂law half (2 * a) b)
      ∂Binomial.law VonNeumann.fairBias n) =
      ∫⁻ k, F (successes + k) ∂law n a b := by
  by_cases h : b ≤ 2 * a
  · simp only [h, ite_true, law, Nat.add_assoc]
    rw [Binomial.filling VonNeumann.fairBias (bias (2 * a - b) b) n
      (fun k => F (successes + k)), high_bias a b hb ha h]
  · simp only [h, ite_false, law]
    rw [Binomial.thinning, low_bias a b hb (by omega)]

/-- Both branches leave half the trials unresolved on average. -/
theorem remaining_mean (n a b : ℕ) :
    (∫⁻ half, ((if b ≤ 2 * a then n - half else half : ℕ) : ℝ≥0∞)
      ∂Binomial.law VonNeumann.fairBias n) = n * (2 : ℝ≥0∞)⁻¹ := by
  have hf : unitInterval.symm VonNeumann.fairBias = VonNeumann.fairBias := by
    apply Subtype.ext
    norm_num [unitInterval.coe_symm_eq, VonNeumann.fairBias]
  by_cases h : b ≤ 2 * a
  · simp only [h, ite_true]
    rw [Binomial.reflection, hf, Binomial.mean]
    norm_num [VonNeumann.fairBias, ENNReal.ofReal_div_of_pos]
  · simp only [h, ite_false]
    rw [Binomial.mean]
    norm_num [VonNeumann.fairBias, ENNReal.ofReal_div_of_pos]

/-- Fixed slack for the amplification induction. -/
def factor : ℝ≥0 := 3 / 2

@[simp] theorem one_lt_factor : 1 < factor := by norm_num [factor]

private theorem remaining_budget (n : ℕ) (hn : 0 < n) :
    (n : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ + factor ≤ n + 1 := by
  have h : (n : ℝ≥0) * (2 : ℝ≥0)⁻¹ + factor ≤ n + 1 := by
    apply (NNReal.coe_le_coe).mp
    norm_num [factor]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h' := ENNReal.coe_le_coe.mpr h
  norm_num at h' ⊢
  exact h'

/-- Conditional binomial credit, unresolved-trial potential, and amplified slack. -/
def refinementCredit (n a b successes : ℕ) (F : ℕ → ℝ≥0∞) (δ : ℝ≥0∞)
    (half : ℕ) : ℝ≥0∞ :=
  ((if b ≤ 2 * a then
    ∫⁻ k, F (successes + half + k) ∂law (n - half) (2 * a - b) b
  else ∫⁻ k, F (successes + k) ∂law half (2 * a) b) +
    (if b ≤ 2 * a then n - half else half : ℕ) * δ) + factor * δ

/-- Halving unresolved trials pays for a fixed amplification of termination credit. -/
theorem expectation_preservation (n a b successes : ℕ) (hb : 0 < b) (ha : a < b)
    (hn : 0 < n) (F : ℕ → ℝ≥0∞) (δ : ℝ≥0∞) :
    (∫⁻ half, refinementCredit n a b successes F δ half
      ∂Binomial.law VonNeumann.fairBias n) ≤
      (∫⁻ k, F (successes + k) ∂law n a b) + n * δ + δ := by
  unfold refinementCredit
  rw [lintegral_add_left (measurable_of_countable _), lintegral_const,
    measure_univ, mul_one, lintegral_add_left (measurable_of_countable _),
    lintegral_mul_const _ (measurable_of_countable _), expectation n a b successes hb ha F,
    remaining_mean]
  calc
    _ = (∫⁻ k, F (successes + k) ∂law n a b) +
        ((n : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ + factor) * δ := by ring
    _ ≤ (∫⁻ k, F (successes + k) ∂law n a b) + (n + 1) * δ := by
      simpa only [add_comm, mul_comm] using
        add_le_add_left (mul_le_mul_right (remaining_budget n hn) δ)
          (∫⁻ k, F (successes + k) ∂law n a b)
    _ = _ := by ring

end

end SampLib.BinomialBinary
