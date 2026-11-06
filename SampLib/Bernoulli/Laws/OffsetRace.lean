import SampLib.Discrete.Laws.WeightedChoice
import SampLib.Uniform.Laws.RealCoin
import SampLib.Bernoulli.Laws.BernoulliRace

/-! # Laws of the Bernoulli race with rational offsets

A uniform rank in three intervals gives an affine coin: certain success, a fresh input coin,
or certain failure. This module proves that interval expectation and computes the two affine
biases that the offset race compares, with their common normalization.
-/

open Finset
open ENNReal (ofReal ofReal_div_of_pos)
open scoped ENNReal

namespace SampLib.OffsetRace

noncomputable section

/-- Bias of a certain-success interval followed by an input-coin interval. -/
def affineBias (p : unitInterval) (a s t : ℕ) (ht : 0 < t) (hast : a + s ≤ t) : unitInterval :=
  ⟨((a : ℝ) + s * (p : ℝ)) / t,
    div_nonneg (add_nonneg (Nat.cast_nonneg a)
      (mul_nonneg (Nat.cast_nonneg s) p.2.1)) (Nat.cast_nonneg t),
    (div_le_one (by exact_mod_cast ht)).mpr (by
      have hat : (a : ℝ) + s ≤ t := by exact_mod_cast hast
      calc
        _ ≤ (a : ℝ) + s := by
          nlinarith [mul_le_mul_of_nonneg_left p.2.2 (Nat.cast_nonneg s)]
        _ ≤ _ := hat)⟩

/-- Credit after observing the common uniform rank. -/
def rankCredit (p : unitInterval) (a s : ℕ) (F : Bool → ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  if k < a then F true else if k < a + s then RealCoin.credit p F else F false

private def categoryCredit (p : unitInterval) (F : Bool → ℝ≥0∞) (j : ℕ) : ℝ≥0∞ :=
  if j = 0 then F true else if j = 1 then RealCoin.credit p F else F false

/-- The three intervals contribute their widths times their conditional credits. -/
private theorem rank_partition (p : unitInterval) (a s t : ℕ) (hast : a + s ≤ t)
    (F : Bool → ℝ≥0∞) :
    (∑ k ∈ range t, rankCredit p a s F k) =
      a * F true + s * RealCoin.credit p F + (t - (a + s) : ℕ) * F false := by
  have hcategory (k : ℕ) : rankCredit p a s F k =
      categoryCredit p F (WeightedChoice.category [a, s, t - (a + s)] k) := by
    by_cases ha : k < a
    · simp [rankCredit, WeightedChoice.category, categoryCredit, ha]
    · by_cases hs : k < a + s
      · have hsub : k - a < s := by omega
        simp [rankCredit, WeightedChoice.category, categoryCredit, ha, hs, hsub]
      · have hsub : ¬k - a < s := by omega
        simp only [rankCredit, ite_eq_right ha, ite_eq_right hs,
          WeightedChoice.category, ite_eq_right hsub]
        split_ifs <;> simp [categoryCredit]
  simp_rw [hcategory]
  have hsum : [a, s, t - (a + s)].sum = t := by simp; omega
  simpa [hsum, WeightedChoice.weightedSum, categoryCredit, add_assoc] using
    WeightedChoice.rank_partition [a, s, t - (a + s)] (categoryCredit p F)

/-- Uniform interval widths give the affine Bernoulli expectation, for all credits. -/
theorem expectation (p : unitInterval) (a s t : ℕ) (ht : 0 < t) (hast : a + s ≤ t)
    (F : Bool → ℝ≥0∞) :
    (∑ k ∈ range t, rankCredit p a s F k) / t =
      RealCoin.credit (affineBias p a s t ht hast) F := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have htrue : ofReal (affineBias p a s t ht hast : ℝ) =
      ((a : ℝ≥0∞) + s * ofReal (p : ℝ)) / t := by
    rw [affineBias, ofReal_div_of_pos htR,
      ENNReal.ofReal_add (Nat.cast_nonneg a) (mul_nonneg (Nat.cast_nonneg s) p.2.1),
      ENNReal.ofReal_mul (Nat.cast_nonneg s)]
    simp
  have hfalse : ofReal (1 - (affineBias p a s t ht hast : ℝ)) =
      ((t - (a + s) : ℕ) + s * ofReal (1 - (p : ℝ))) / t := by
    have heq : 1 - (affineBias p a s t ht hast : ℝ) =
        (((t - (a + s) : ℕ) : ℝ) + s * (1 - (p : ℝ))) / t := by
      simp only [affineBias, Nat.cast_sub hast, Nat.cast_add]
      field_simp
      ring
    rw [heq, ofReal_div_of_pos htR,
      ENNReal.ofReal_add (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg s)
        (sub_nonneg.mpr p.2.2)), ENNReal.ofReal_mul (Nat.cast_nonneg s)]
    simp
  rw [rank_partition p a s t hast F]
  simp only [RealCoin.credit, RealCoin.pmf, ite_true, Bool.false_eq_true, ite_false,
    htrue, hfalse, ENNReal.div_eq_inv_mul]
  ring

/-- Total rank range shared by both affine coins. -/
def total (a b x y : ℕ) : ℕ := a * y + x * b + b * y

theorem total_pos (a b x y : ℕ) (hb : 0 < b) (hy : 0 < y) :
    0 < total a b x y := by
  have hs := Nat.mul_pos hb hy
  unfold total
  omega

theorem left_bound (a b x y : ℕ) : x * b + b * y ≤ total a b x y := by
  unfold total
  omega

theorem right_bound (a b x y : ℕ) : a * y + b * y ≤ total a b x y := by
  unfold total
  omega

/-- Affine coin for the `x/y + q` side of the race. -/
def leftBias (q : unitInterval) (a b x y : ℕ) (hb : 0 < b) (hy : 0 < y) :=
  affineBias q (x * b) (b * y) (total a b x y) (total_pos a b x y hb hy)
    (left_bound a b x y)

/-- Affine coin for the `a/b + p` side of the race. -/
def rightBias (p : unitInterval) (a b x y : ℕ) (hb : 0 < b) (hy : 0 < y) :=
  affineBias p (a * y) (b * y) (total a b x y) (total_pos a b x y hb hy)
    (right_bound a b x y)

/-- Common normalization of both affine coins. -/
def normalizer (a b x y : ℕ) : ℝ := (b * y : ℕ) / (total a b x y : ℝ)

theorem normalizer_pos (a b x y : ℕ) (hb : 0 < b) (hy : 0 < y) :
    0 < normalizer a b x y :=
  div_pos (by exact_mod_cast Nat.mul_pos hb hy) (by exact_mod_cast total_pos a b x y hb hy)

theorem left_coe (q : unitInterval) (a b x y : ℕ) (hb : 0 < b) (hy : 0 < y) :
    (leftBias q a b x y hb hy : ℝ) = normalizer a b x y * ((x : ℝ) / y + (q : ℝ)) := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast hy.ne'
  have htR : (total a b x y : ℝ) ≠ 0 := by
    exact_mod_cast (total_pos a b x y hb hy).ne'
  change (((x * b : ℕ) : ℝ) + (b * y : ℕ) * (q : ℝ)) / (total a b x y) = _
  simp only [normalizer, Nat.cast_mul]
  field_simp

theorem right_coe (p : unitInterval) (a b x y : ℕ) (hb : 0 < b) (hy : 0 < y) :
    (rightBias p a b x y hb hy : ℝ) = normalizer a b x y * ((a : ℝ) / b + (p : ℝ)) := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast hy.ne'
  have htR : (total a b x y : ℝ) ≠ 0 := by
    exact_mod_cast (total_pos a b x y hb hy).ne'
  change (((a * y : ℕ) : ℝ) + (b * y : ℕ) * (p : ℝ)) / (total a b x y) = _
  simp only [normalizer, Nat.cast_mul]
  field_simp

theorem sum_coe (p q : unitInterval) (a b x y : ℕ) (hb : 0 < b) (hy : 0 < y) :
    (leftBias q a b x y hb hy : ℝ) + (rightBias p a b x y hb hy : ℝ) =
      normalizer a b x y * ((a : ℝ) / b + (p : ℝ) + (x : ℝ) / y + (q : ℝ)) := by
  rw [left_coe, right_coe]
  ring

/-- A positive offset ratio denominator gives the race positive exit mass. -/
theorem race_pos (p q : unitInterval) (a b x y : ℕ) (hb : 0 < b) (hy : 0 < y)
    (h : 0 < (a : ℝ) / b + (p : ℝ) + (x : ℝ) / y + (q : ℝ)) :
    0 < (leftBias q a b x y hb hy : ℝ) + (rightBias p a b x y hb hy : ℝ) := by
  rw [sum_coe]
  exact mul_pos (normalizer_pos a b x y hb hy) h

/-- Race the two affine coins using their common uniform-rank normalization. -/
def bias (p q : unitInterval) (a b x y : ℕ) (hb : 0 < b) (hy : 0 < y) : unitInterval :=
  BernoulliRace.bias (leftBias q a b x y hb hy) (rightBias p a b x y hb hy)

/-- The common normalization cancels, leaving the advertised offset ratio. -/
theorem bias_coe (p q : unitInterval) (a b x y : ℕ) (hb : 0 < b) (hy : 0 < y) :
    (bias p q a b x y hb hy : ℝ) = ((x : ℝ) / y + (q : ℝ)) /
      ((a : ℝ) / b + (p : ℝ) + (x : ℝ) / y + (q : ℝ)) := by
  change (leftBias q a b x y hb hy : ℝ) /
    ((leftBias q a b x y hb hy : ℝ) + (rightBias p a b x y hb hy : ℝ)) = _
  rw [sum_coe, left_coe, mul_div_mul_left _ _ (normalizer_pos a b x y hb hy).ne']

end

end SampLib.OffsetRace
