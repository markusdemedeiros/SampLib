import SampLib.Bernoulli.Laws.BernoulliRetry

/-! # Laws of the reciprocal affine factory

A uniform rank selects a successful exit, an unsuccessful exit, or an input-coin trial. The
three interval widths identify the normalized reciprocal affine law `d/(c+s*p)` and fund the
amplified retry credit.
-/

open Finset
open ENNReal (ofReal ofReal_add ofReal_mul)
open scoped ENNReal NNReal

namespace SampLib.ReciprocalAffine

noncomputable section

private theorem denominator_pos (p : unitInterval) (c s : ℕ) (hc : 0 < c) :
    0 < (c : ℝ) + s * (p : ℝ) :=
  add_pos_of_pos_of_nonneg (by exact_mod_cast hc) (mul_nonneg (Nat.cast_nonneg s) p.2.1)

/-- Bias `d/(c+s*p)` for disjoint integer exit widths `d≤c`. -/
def bias (p : unitInterval) (c d s : ℕ) (hc : 0 < c) (hd : d ≤ c) : unitInterval :=
  ⟨(d : ℝ) / ((c : ℝ) + s * (p : ℝ)),
    div_nonneg (Nat.cast_nonneg d) (denominator_pos p c s hc).le,
    (div_le_one (denominator_pos p c s hc)).mpr (by
      have hdc : (d : ℝ) ≤ c := by exact_mod_cast hd
      exact hdc.trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg s) p.2.1)))⟩

/-- Probability of selecting the input interval and observing a failure. -/
def retry (p : unitInterval) (c s : ℕ) (hc : 0 < c) : unitInterval :=
  ⟨s * (1 - (p : ℝ)) / (c + s),
    div_nonneg (mul_nonneg (Nat.cast_nonneg s) (sub_nonneg.mpr p.2.2)) (by positivity),
    (div_le_one (by positivity : (0 : ℝ) < c + s)).mpr (by
      have hcR : (0 : ℝ) < c := by exact_mod_cast hc
      nlinarith [mul_nonneg (Nat.cast_nonneg s) p.2.1])⟩

@[simp] private theorem retry_coe (p : unitInterval) (c s : ℕ) (hc : 0 < c) :
    (retry p c s hc : ℝ) = s * (1 - (p : ℝ)) / (c + s) := rfl

/-- The retry branch has probability below one, so retries terminate. -/
theorem retry_lt_one (p : unitInterval) (c s : ℕ) (hc : 0 < c) :
    (retry p c s hc : ℝ) < 1 := by
  change (s : ℝ) * (1 - (p : ℝ)) / (c + s) < 1
  rw [div_lt_one (by positivity : (0 : ℝ) < c + s)]
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  nlinarith [mul_nonneg (Nat.cast_nonneg s) p.2.1]

/-- Credit after the input coin, with amplified credit on its retry branch. -/
def coinCredit (p : unitInterval) (c d s : ℕ) (hc : 0 < c) (hd : d ≤ c)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F false else RealCoin.credit (bias p c d s hc hd) F +
    BernoulliRetry.factor (retry p c s hc) * ε

/-- Credit assigned to a rank in the three consecutive intervals. -/
def rankCredit (p : unitInterval) (c d s : ℕ) (hc : 0 < c) (hd : d ≤ c)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  if k < d then F true else if k < c then F false else
    ∫⁻ b, coinCredit p c d s hc hd F ε b ∂RealCoin.law p

private theorem rank_partition (c d s : ℕ) (hd : d ≤ c) (A B C : ℝ≥0∞) :
    ∑ k ∈ range (c + s), (if k < d then A else if k < c then B else C) =
      d * A + ((c - d : ℕ) : ℝ≥0∞) * B + s * C := by
  have hsum : c + s = d + ((c - d) + s) := by omega
  rw [hsum, sum_range_add, sum_range_add]
  have hfirst : (∑ k ∈ range d, if k < d then A else if k < c then B else C) = d * A := by
    calc
      _ = ∑ k ∈ range d, A := sum_congr rfl fun k hk => by simp [mem_range.mp hk]
      _ = _ := by simp [nsmul_eq_mul]
  have hsecond : (∑ k ∈ range (c - d),
      if d + k < d then A else if d + k < c then B else C) = ((c - d : ℕ) : ℝ≥0∞) * B := by
    calc
      _ = ∑ k ∈ range (c - d), B := sum_congr rfl fun k hk => by
        have hk' := mem_range.mp hk
        simp [show ¬d + k < d by omega, show d + k < c by omega]
      _ = _ := by simp [nsmul_eq_mul]
  rw [hfirst, hsecond]
  simp [show ∀ k : ℕ, ¬d + (c - d + k) < d by omega,
    show ∀ k : ℕ, ¬d + (c - d + k) < c by omega, nsmul_eq_mul, add_assoc]

/-- The three interval widths balance the reciprocal law and fund retries. -/
theorem expectation (p : unitInterval) (c d s : ℕ) (hc : 0 < c) (hd : d ≤ c)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∑ k ∈ range (c + s), rankCredit p c d s hc hd F ε k) / ((c + s : ℕ) : ℝ≥0∞) ≤
      RealCoin.credit (bias p c d s hc hd) F + ε := by
  let a : ℝ := d / (c + s)
  let b : ℝ := ((c - d : ℕ) + s * (p : ℝ)) / (c + s)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b :=
    div_nonneg (add_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) p.2.1))
      (by positivity)
  have hsum : a + b + (retry p c s hc : ℝ) = 1 := by
    dsimp [a, b, retry]
    rw [Nat.cast_sub hd]
    field_simp
    ring
  have hnormalized : BernoulliRetry.bias a b ha hb = bias p c d s hc hd := by
    apply Subtype.ext
    change a / (a + b) = (d : ℝ) / ((c : ℝ) + s * (p : ℝ))
    have hT : (c : ℝ) + s ≠ 0 := by positivity
    have hab : a + b = ((c : ℝ) + s * (p : ℝ)) / (c + s) := by
      dsimp [a, b]
      rw [Nat.cast_sub hd]
      ring
    rw [hab]
    exact div_div_div_cancel_right₀ hT _ _
  have h := BernoulliRetry.expectation a b ha hb (retry p c s hc)
    (retry_lt_one p c s hc) hsum F ε
  rw [hnormalized] at h
  calc
    _ = ofReal a * F true + ofReal b * F false + ofReal (retry p c s hc : ℝ) *
        (RealCoin.credit (bias p c d s hc hd) F +
          BernoulliRetry.factor (retry p c s hc) * ε) := by
      simp only [rankCredit, Nat.cast_add]
      rw [rank_partition c d s hd]
      simp only [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf, coinCredit,
        ite_true, Bool.false_eq_true, ite_false]
      dsimp [a, b]
      simp only [ENNReal.ofReal_div_of_pos
        (by positivity : (0 : ℝ) < c + s)]
      rw [ofReal_add (Nat.cast_nonneg (c - d)) (mul_nonneg (Nat.cast_nonneg s) p.2.1)]
      simp only [ofReal_add (Nat.cast_nonneg c) (Nat.cast_nonneg s),
        ofReal_mul (Nat.cast_nonneg s), ENNReal.ofReal_natCast,
        ENNReal.div_eq_inv_mul]
      ring
    _ ≤ _ := h

end

end SampLib.ReciprocalAffine
