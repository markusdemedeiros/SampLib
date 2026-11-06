import SampLib.Bernoulli.Division
import SampLib.Bernoulli.Laws.BernoulliRetry
import SampLib.Bernoulli.OffsetRace

/-! # Ratios of affine coin probabilities

The direct branch partitions a uniform trial into two exits and a retry. The
other branch divides two affine coins with their common rank normalization.
-/

open Set MeasureTheory Finset
open ENNReal (ofReal ofReal_div_of_pos)
open scoped ENNReal NNReal

namespace SampLib.AffineRatio

noncomputable section

def numerator (q : unitInterval) (d s : ℕ) : ℝ := d + s * (q : ℝ)

def denominator (p : unitInterval) (c s : ℕ) : ℝ := c + s * (p : ℝ)

/-- Direct rejection ignores the margin; division uses the normalized positive gap. -/
def Admissible (p q : unitInterval) (c d s : ℕ) (e f : ℤ) : Prop :=
  d + s ≤ c ∨ (0 < e ∧ e < f ∧ (e : ℝ) / f ≤
    (denominator p c s - numerator q d s) / ((c + d + s : ℕ) : ℝ))

private theorem numerator_nonneg (q : unitInterval) (d s : ℕ) : 0 ≤ numerator q d s :=
  add_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) q.2.1)

theorem bounds (p q : unitInterval) (c d s : ℕ) (e f : ℤ) (hs : 0 < s)
    (h : Admissible p q c d s e f) :
    0 < denominator p c s ∧ numerator q d s ≤ denominator p c s := by
  rcases h with hd | ⟨he, hef, hgap⟩
  · have hc : 0 < c := lt_of_lt_of_le (lt_of_lt_of_le hs (Nat.le_add_left _ _)) hd
    have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
    have hds : (d : ℝ) + s ≤ c := by exact_mod_cast hd
    have hnum : numerator q d s ≤ c := by
      dsimp [numerator]
      nlinarith [mul_le_mul_of_nonneg_left q.2.2 (Nat.cast_nonneg s)]
    have hden : (c : ℝ) ≤ denominator p c s :=
      le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) p.2.1)
    exact ⟨hcR.trans_le hden, hnum.trans hden⟩
  · have hT : 0 < ((c + d + s : ℕ) : ℝ) := by exact_mod_cast (show 0 < c + d + s by omega)
    have hε : 0 < (e : ℝ) / f :=
      div_pos (by exact_mod_cast he) (by exact_mod_cast he.trans hef)
    have hpos := (div_pos_iff_of_pos_right hT).mp (hε.trans_le hgap)
    exact ⟨lt_of_le_of_lt (numerator_nonneg q d s) (sub_pos.mp hpos),
      (sub_pos.mp hpos).le⟩

/-- The normalized affine ratio; the domain ensures its denominator is positive. -/
def bias (p q : unitInterval) (c d s : ℕ) (e f : ℤ) (hs : 0 < s)
    (h : Admissible p q c d s e f) : unitInterval :=
  ⟨numerator q d s / denominator p c s,
    div_nonneg (numerator_nonneg q d s) (bounds p q c d s e f hs h).1.le,
    (div_le_one (bounds p q c d s e f hs h).1).mpr (bounds p q c d s e f hs h).2⟩

def directBias (p q : unitInterval) (c d s : ℕ) (hs : 0 < s) (h : d + s ≤ c) :
    unitInterval := bias p q c d s 0 0 hs (Or.inl h)

theorem bias_eq_direct (p q : unitInterval) (c d s : ℕ) (e f : ℤ) (hs : 0 < s)
    (h : Admissible p q c d s e f) (hd : d + s ≤ c) :
    bias p q c d s e f hs h = directBias p q c d s hs hd := rfl

def success (q : unitInterval) (c d s : ℕ) : ℝ :=
  numerator q d s / ((c + s : ℕ) : ℝ)

def failure (p q : unitInterval) (c d s : ℕ) : ℝ :=
  ((c : ℝ) - d - s * (q : ℝ) + s * (p : ℝ)) / ((c + s : ℕ) : ℝ)

private theorem success_nonneg (q : unitInterval) (c d s : ℕ) : 0 ≤ success q c d s :=
  div_nonneg (numerator_nonneg q d s) (Nat.cast_nonneg _)

private theorem failure_nonneg (p q : unitInterval) (c d s : ℕ) (h : d + s ≤ c) :
    0 ≤ failure p q c d s := by
  have hds : (d : ℝ) + s ≤ c := by exact_mod_cast h
  apply div_nonneg _ (Nat.cast_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left q.2.2 (Nat.cast_nonneg s),
    mul_nonneg (Nat.cast_nonneg s) p.2.1]

def retry (p : unitInterval) (c s : ℕ) (hs : 0 < s) : unitInterval :=
  ⟨(s : ℝ) * (1 - (p : ℝ)) / ((c + s : ℕ) : ℝ),
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr p.2.2)) (Nat.cast_nonneg _),
    (div_le_one (by exact_mod_cast (show 0 < c + s by omega))).mpr (by
      have hp := mul_nonneg (Nat.cast_nonneg s) p.2.1
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) c])⟩

theorem retry_lt_one (p : unitInterval) (c d s : ℕ) (hs : 0 < s) (h : d + s ≤ c) :
    (retry p c s hs : ℝ) < 1 := by
  have hc : 0 < c := by omega
  apply (div_lt_one (by exact_mod_cast (show 0 < c + s by omega))).mpr
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  push_cast
  nlinarith [mul_nonneg (Nat.cast_nonneg s) p.2.1]

private theorem trial_partition (p q : unitInterval) (c d s : ℕ) (hs : 0 < s) :
    success q c d s + failure p q c d s + (retry p c s hs : ℝ) = 1 := by
  have hT : (c + s : ℕ) ≠ 0 := by omega
  dsimp [success, failure, numerator, retry]
  field_simp
  push_cast
  ring

private theorem accepted_bias (p q : unitInterval) (c d s : ℕ) (hs : 0 < s)
    (h : d + s ≤ c) :
    BernoulliRetry.bias (success q c d s) (failure p q c d s)
      (success_nonneg q c d s) (failure_nonneg p q c d s h) = directBias p q c d s hs h := by
  have hT : ((c + s : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show c + s ≠ 0 by omega)
  have hd := (bounds p q c d s 0 0 hs (Or.inl h)).1.ne'
  apply Subtype.ext
  change success q c d s / (success q c d s + failure p q c d s) =
    numerator q d s / denominator p c s
  have hsum : success q c d s + failure p q c d s =
      denominator p c s / ((c + s : ℕ) : ℝ) := by
    dsimp [success, failure, numerator, denominator]
    ring
  rw [hsum]
  dsimp [success]
  field_simp

def coinCredit (p q : unitInterval) (c d s : ℕ) (hs : 0 < s) (h : d + s ≤ c)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F false else RealCoin.credit (directBias p q c d s hs h) F +
    BernoulliRetry.factor (retry p c s hs) * ε

def rankCredit (p q : unitInterval) (c d s : ℕ) (hs : 0 < s) (h : d + s ≤ c)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  if k < d then F true else if k < d + s then ∫⁻ b, F b ∂RealCoin.law q
  else if k < c then F false else ∫⁻ b, coinCredit p q c d s hs h F ε b ∂RealCoin.law p

private def categoryCredit (p q : unitInterval) (c d s : ℕ) (hs : 0 < s) (h : d + s ≤ c)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (j : ℕ) : ℝ≥0∞ :=
  if j = 0 then F true else if j = 1 then ∫⁻ b, F b ∂RealCoin.law q
  else if j = 2 then F false else ∫⁻ b, coinCredit p q c d s hs h F ε b ∂RealCoin.law p

private theorem rank_partition (p q : unitInterval) (c d s : ℕ) (hs : 0 < s)
    (h : d + s ≤ c) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∑ k ∈ range (c + s), rankCredit p q c d s hs h F ε k) =
      d * F true + s * (∫⁻ b, F b ∂RealCoin.law q) +
        (c - (d + s) : ℕ) * F false +
        s * (∫⁻ b, coinCredit p q c d s hs h F ε b ∂RealCoin.law p) := by
  have hcategory (k : ℕ) : rankCredit p q c d s hs h F ε k =
      categoryCredit p q c d s hs h F ε
        (WeightedChoice.category [d, s, c - (d + s), s] k) := by
    by_cases hd : k < d
    · simp [rankCredit, WeightedChoice.category, categoryCredit, hd]
    · by_cases hds : k < d + s
      · have hk : k - d < s := by omega
        simp [rankCredit, WeightedChoice.category, categoryCredit, hd, hds, hk]
      · have hk : ¬k - d < s := by omega
        by_cases hc : k < c
        · have hkc : k - d - s < c - (d + s) := by omega
          simp [rankCredit, WeightedChoice.category, categoryCredit, hd, hds, hk, hc, hkc]
        · have hkc : ¬k - d - s < c - (d + s) := by omega
          simp only [rankCredit, ite_eq_right hd, ite_eq_right hds, ite_eq_right hc,
            WeightedChoice.category, ite_eq_right hk, ite_eq_right hkc]
          split_ifs <;> simp [categoryCredit]
  simp_rw [hcategory]
  have hsum : [d, s, c - (d + s), s].sum = c + s := by simp; omega
  simpa [hsum, WeightedChoice.weightedSum, categoryCredit, add_assoc] using
    WeightedChoice.rank_partition [d, s, c - (d + s), s]
      (categoryCredit p q c d s hs h F ε)

/-- Accepted interval masses identify the ratio; the remaining interval finances retries. -/
theorem direct_expectation (p q : unitInterval) (c d s : ℕ) (hs : 0 < s)
    (h : d + s ≤ c) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∑ k ∈ range (c + s), rankCredit p q c d s hs h F ε k) / (c + s : ℕ) ≤
      RealCoin.credit (directBias p q c d s hs h) F + ε := by
  have hT : (0 : ℝ) < (c + s : ℕ) := by exact_mod_cast (show 0 < c + s by omega)
  have ht : ofReal (success q c d s) =
      ((d : ℝ≥0∞) + s * ofReal (q : ℝ)) / (c + s : ℕ) := by
    rw [success, numerator, ofReal_div_of_pos hT,
      ENNReal.ofReal_add (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) q.2.1),
      ENNReal.ofReal_mul (Nat.cast_nonneg s)]
    simp only [ENNReal.ofReal_natCast]
  have hf : ofReal (failure p q c d s) =
      (((c - (d + s) : ℕ) : ℝ≥0∞) + s * ofReal (1 - (q : ℝ)) + s * ofReal (p : ℝ)) /
        (c + s : ℕ) := by
    have hn : (c : ℝ) - d - s * (q : ℝ) + s * (p : ℝ) =
        ((c - (d + s) : ℕ) : ℝ) + s * (1 - (q : ℝ)) + s * (p : ℝ) := by
      rw [Nat.cast_sub h, Nat.cast_add]
      ring
    rw [failure, hn, ofReal_div_of_pos hT,
      ENNReal.ofReal_add (add_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr q.2.2)))
        (mul_nonneg (Nat.cast_nonneg _) p.2.1),
      ENNReal.ofReal_add (Nat.cast_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr q.2.2)),
      ENNReal.ofReal_mul (Nat.cast_nonneg s), ENNReal.ofReal_mul (Nat.cast_nonneg s)]
    simp only [ENNReal.ofReal_natCast]
  have hr : ofReal (retry p c s hs : ℝ) =
      s * ofReal (1 - (p : ℝ)) / (c + s : ℕ) := by
    change ofReal ((s : ℝ) * (1 - (p : ℝ)) / ((c + s : ℕ) : ℝ)) = _
    rw [ofReal_div_of_pos hT, ENNReal.ofReal_mul (Nat.cast_nonneg s)]
    simp only [ENNReal.ofReal_natCast]
  calc
    _ = ofReal (success q c d s) * F true + ofReal (failure p q c d s) * F false +
        ofReal (retry p c s hs : ℝ) *
          (RealCoin.credit (directBias p q c d s hs h) F +
            BernoulliRetry.factor (retry p c s hs) * ε) := by
      rw [rank_partition p q c d s hs h F ε, ht, hf, hr]
      simp only [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf, coinCredit,
        ite_true, Bool.false_eq_true, ite_false, ENNReal.div_eq_inv_mul]
      ring
    _ ≤ _ := by
      have he := BernoulliRetry.expectation _ _ (success_nonneg q c d s)
        (failure_nonneg p q c d s h) (retry p c s hs) (retry_lt_one p c d s hs h)
        (trial_partition p q c d s hs) F ε
      simpa only [accepted_bias p q c d s hs h] using he

theorem interval_bounds (c d s : ℕ) : c + s ≤ c + d + s ∧ d + s ≤ c + d + s := by
  omega

def denominatorBias (p : unitInterval) (c d s : ℕ) (hs : 0 < s) : unitInterval :=
  OffsetRace.affineBias p c s (c + d + s) (Nat.add_pos_right _ hs) (interval_bounds c d s).1

def numeratorBias (q : unitInterval) (c d s : ℕ) (hs : 0 < s) : unitInterval :=
  OffsetRace.affineBias q d s (c + d + s) (Nat.add_pos_right _ hs) (interval_bounds c d s).2

@[simp] theorem denominatorBias_coe (p : unitInterval) (c d s : ℕ) (hs : 0 < s) :
    (denominatorBias p c d s hs : ℝ) = denominator p c s / ((c + d + s : ℕ) : ℝ) := rfl

@[simp] theorem numeratorBias_coe (q : unitInterval) (c d s : ℕ) (hs : 0 < s) :
    (numeratorBias q c d s hs : ℝ) = numerator q d s / ((c + d + s : ℕ) : ℝ) := rfl

/-- Failure of the direct test exposes exactly the division factory's supplied margin. -/
theorem division_parameters (p q : unitInterval) (c d s : ℕ) (e f : ℤ) (hs : 0 < s)
    (h : Admissible p q c d s e f) (hd : ¬d + s ≤ c) :
    0 < e ∧ e < f ∧ (e : ℝ) / f ≤
      (denominatorBias p c d s hs : ℝ) - numeratorBias q c d s hs := by
  rcases h with hdir | ⟨he, hef, hgap⟩
  · exact (hd hdir).elim
  · refine ⟨he, hef, ?_⟩
    rw [denominatorBias_coe, numeratorBias_coe, ← sub_div]
    exact hgap

/-- The common rank normalization cancels in the verified division law. -/
theorem division_bias_eq (p q : unitInterval) (c d s : ℕ) (e f : ℤ) (hs : 0 < s)
    (h : Admissible p q c d s e f) (hd : ¬d + s ≤ c) :
    Division.bias (denominatorBias p c d s hs) (numeratorBias q c d s hs) e f
      (division_parameters p q c d s e f hs h hd).1
      (division_parameters p q c d s e f hs h hd).2.1
      (division_parameters p q c d s e f hs h hd).2.2 = bias p q c d s e f hs h := by
  apply Subtype.ext
  rw [Division.bias_coe, denominatorBias_coe, numeratorBias_coe]
  change (numerator q d s / ((c + d + s : ℕ) : ℝ)) /
    (denominator p c s / ((c + d + s : ℕ) : ℝ)) = numerator q d s / denominator p c s
  have hT : ((c + d + s : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.add_pos_right (c + d) hs).ne'
  have hden := (bounds p q c d s e f hs h).1.ne'
  field_simp

/-- Width scaling recovers the requested ratio of rational offsets. -/
theorem bias_coe (p q : unitInterval) (a b x y : ℕ) (e f : ℤ) (hb : 0 < b) (hy : 0 < y)
    (h : Admissible p q (a * y) (x * b) (b * y) e f) :
    (bias p q (a * y) (x * b) (b * y) e f (Nat.mul_pos hb hy) h : ℝ) =
      ((x : ℝ) / y + q) / ((a : ℝ) / b + p) := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast hy.ne'
  have hsR : ((b * y : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hb hy).ne'
  have hn : numerator q (x * b) (b * y) =
      ((b * y : ℕ) : ℝ) * ((x : ℝ) / y + q) := by
    dsimp [numerator]
    push_cast
    field_simp
  have hd : denominator p (a * y) (b * y) =
      ((b * y : ℕ) : ℝ) * ((a : ℝ) / b + p) := by
    dsimp [denominator]
    push_cast
    field_simp
  change numerator q (x * b) (b * y) / denominator p (a * y) (b * y) = _
  rw [hn, hd, mul_div_mul_left _ _ hsR]

end

end SampLib.AffineRatio
