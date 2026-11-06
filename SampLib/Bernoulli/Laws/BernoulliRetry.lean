import SampLib.Uniform.Laws.RealCoin

/-! # Bernoulli laws from accepted and retried trials

A trial exits with masses `a` and `b`, or retries with mass `q`. Its eventual
success bias is `a/(a+b)`. The same balance identity funds arbitrary continuation
credits and the auxiliary credit needed to prove termination.
-/

open ENNReal (ofReal ofReal_add ofReal_mul)
open scoped ENNReal NNReal

namespace SampLib.BernoulliRetry

noncomputable section

/-- The normalized mass of the successful exit. -/
def bias (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : unitInterval :=
  ⟨a / (a + b), div_nonneg ha (add_nonneg ha hb), by
    by_cases h : a + b = 0
    · simp [h]
    · exact (div_le_one (lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm h))).mpr
        (le_add_of_nonneg_right hb)⟩

/-- Retry credit grows by a factor strictly larger than one whenever `q<1`. -/
def factor (q : unitInterval) : ℝ≥0 :=
  ⟨2 / (1 + (q : ℝ)), div_nonneg (by norm_num) (by linarith [q.2.1])⟩

theorem one_lt_factor (q : unitInterval) (hq : (q : ℝ) < 1) : 1 < factor q := by
  exact_mod_cast (one_lt_div (by linarith [q.2.1] : 0 < 1 + (q : ℝ))).mpr
    (by linarith : 1 + (q : ℝ) < 2)

/-- Accepted masses identify the Bernoulli expectation; retries consume at most `ε`. -/
theorem expectation (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (q : unitInterval)
    (hq : (q : ℝ) < 1) (hsum : a + b + (q : ℝ) = 1)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    ofReal a * F true + ofReal b * F false +
      ofReal (q : ℝ) * (RealCoin.credit (bias a b ha hb) F + factor q * ε) ≤
        RealCoin.credit (bias a b ha hb) F + ε := by
  have hab : 0 < a + b := by linarith
  have ht := (bias a b ha hb).2.1
  have hf := sub_nonneg.mpr (bias a b ha hb).2.2
  change 0 ≤ a / (a + b) at ht
  change 0 ≤ 1 - a / (a + b) at hf
  have htrue : ofReal a + ofReal (q : ℝ) * RealCoin.pmf (bias a b ha hb) true =
      RealCoin.pmf (bias a b ha hb) true := by
    change ofReal a + ofReal (q : ℝ) * ofReal (a / (a + b)) = ofReal (a / (a + b))
    rw [← ofReal_mul q.2.1, ← ofReal_add ha (mul_nonneg q.2.1 ht)]
    congr 1
    field_simp [hab.ne']
    linear_combination a * hsum
  have hfalse : ofReal b + ofReal (q : ℝ) * RealCoin.pmf (bias a b ha hb) false =
      RealCoin.pmf (bias a b ha hb) false := by
    change ofReal b + ofReal (q : ℝ) * ofReal (1 - a / (a + b)) =
      ofReal (1 - a / (a + b))
    rw [← ofReal_mul q.2.1, ← ofReal_add hb (mul_nonneg q.2.1 hf)]
    congr 1
    field_simp [hab.ne']
    linear_combination b * hsum
  have hamp : ofReal (q : ℝ) * (factor q : ℝ≥0∞) ≤ 1 := by
    rw [ENNReal.coe_nnreal_eq]
    change ofReal (q : ℝ) * ofReal (2 / (1 + (q : ℝ))) ≤ 1
    rw [← ofReal_mul q.2.1]
    apply ENNReal.ofReal_le_one.mpr
    rw [← mul_div_assoc, div_le_one (by linarith [q.2.1] : 0 < 1 + (q : ℝ))]
    linarith [q.2.2]
  calc
    _ = (ofReal a + ofReal (q : ℝ) * RealCoin.pmf (bias a b ha hb) true) * F true +
        (ofReal b + ofReal (q : ℝ) * RealCoin.pmf (bias a b ha hb) false) * F false +
        (ofReal (q : ℝ) * (factor q : ℝ≥0∞)) * ε := by
      simp only [RealCoin.credit]
      ring
    _ ≤ _ := by
      rw [htrue, hfalse]
      exact add_le_add le_rfl (mul_le_of_le_one_left' hamp)

end

end SampLib.BernoulliRetry
