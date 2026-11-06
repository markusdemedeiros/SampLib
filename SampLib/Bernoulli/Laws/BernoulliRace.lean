import SampLib.Bernoulli.Laws.VonNeumann

/-! # Laws of the Bernoulli race

A fair selector picks a side and flips that side's coin. A success returns the side, and a
failure retries, so the output bias is `p/(p+q)`. Each retry amplifies the remaining credit
by `factor p q`, which pays for termination whenever `p+q > 0`.
-/

open ENNReal (ofReal ofReal_add ofReal_mul coe_nnreal_eq)
open scoped ENNReal NNReal

namespace SampLib.BernoulliRace

open RealCoin (pmf lintegral_law)

noncomputable section

def bias (p q : unitInterval) : unitInterval :=
  ⟨(p : ℝ) / ((p : ℝ) + q), div_nonneg p.2.1 (add_nonneg p.2.1 q.2.1), by
    by_cases hsum : (p : ℝ) + q = 0
    · simp [hsum]
    · apply (div_le_one (lt_of_le_of_ne (add_nonneg p.2.1 q.2.1) (Ne.symm hsum))).2
      linarith [q.2.1]⟩

abbrev law (p q : unitInterval) := RealCoin.law (bias p q)
abbrev credit (p q : unitInterval) := RealCoin.credit (bias p q)

section termination

private def retryProbability (p q : unitInterval) : ℝ := 1 - ((p : ℝ) + q) / 2

private theorem retryProbability_nonneg (p q : unitInterval) : 0 ≤ retryProbability p q := by
  dsimp [retryProbability]
  linarith [p.2.2, q.2.2]

def factor (p q : unitInterval) : ℝ≥0 :=
  ⟨2 / (1 + retryProbability p q), div_nonneg (by norm_num)
    (by linarith [retryProbability_nonneg p q])⟩

theorem one_lt_factor (p q : unitInterval) (hsum : 0 < (p : ℝ) + q) :
    1 < factor p q := by
  have hr : retryProbability p q < 1 := by dsimp [retryProbability]; linarith
  have hd : 0 < 1 + retryProbability p q := by linarith [retryProbability_nonneg p q]
  exact_mod_cast (one_lt_div hd).2 (by linarith : 1 + retryProbability p q < 2)

end termination

def coinCredit (p q : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞)
    (side success : Bool) : ℝ≥0∞ :=
  if success then F side else credit p q F + factor p q * ε

def fairCredit (p q : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (side : Bool) : ℝ≥0∞ :=
  if side then ∫⁻ b, coinCredit p q F ε true b ∂RealCoin.law p
  else ∫⁻ b, coinCredit p q F ε false b ∂RealCoin.law q

/-- Both success exits balance the target ratio; failed attempts spend at most `ε`. -/
theorem expectation (p q : unitInterval) (hsum : 0 < (p : ℝ) + q)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ side, fairCredit p q F ε side ∂RealCoin.law VonNeumann.fairBias ≤ credit p q F + ε := by
  have hr := retryProbability_nonneg p q
  have ht : 0 ≤ (p : ℝ) / ((p : ℝ) + q) := (bias p q).2.1
  have hf : 0 ≤ 1 - (p : ℝ) / ((p : ℝ) + q) := sub_nonneg.mpr (bias p q).2.2
  have hsplit : ofReal (retryProbability p q) =
      ofReal (1 / 2 : ℝ) * (pmf p false + pmf q false) := by
    rw [show retryProbability p q = (1 / 2 : ℝ) * ((1 - (p : ℝ)) + (1 - (q : ℝ))) by
      dsimp [retryProbability]; ring, ofReal_mul (by norm_num),
      ofReal_add (sub_nonneg.mpr p.2.2) (sub_nonneg.mpr q.2.2)]
    simp [pmf]
  have htrue : ofReal (retryProbability p q) * pmf (bias p q) true +
      ofReal (1 / 2 : ℝ) * pmf p true = pmf (bias p q) true := by
    change ofReal (retryProbability p q) * ofReal ((p : ℝ) / ((p : ℝ) + q)) +
      ofReal (1 / 2 : ℝ) * ofReal (p : ℝ) = ofReal ((p : ℝ) / ((p : ℝ) + q))
    rw [← ofReal_mul hr, ← ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ofReal_add (mul_nonneg hr ht) (mul_nonneg (by norm_num) p.2.1)]
    congr 1
    dsimp [retryProbability]
    field_simp [hsum.ne']
    ring
  have hfalse : ofReal (retryProbability p q) * pmf (bias p q) false +
      ofReal (1 / 2 : ℝ) * pmf q true = pmf (bias p q) false := by
    change ofReal (retryProbability p q) * ofReal (1 - (p : ℝ) / ((p : ℝ) + q)) +
      ofReal (1 / 2 : ℝ) * ofReal (q : ℝ) = ofReal (1 - (p : ℝ) / ((p : ℝ) + q))
    rw [← ofReal_mul hr, ← ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ofReal_add (mul_nonneg hr hf) (mul_nonneg (by norm_num) q.2.1)]
    congr 1
    dsimp [retryProbability]
    field_simp [hsum.ne']
    ring
  have hterm : ofReal (retryProbability p q) * (factor p q : ℝ≥0∞) ≤ 1 := by
    rw [coe_nnreal_eq]
    change ofReal (retryProbability p q) * ofReal (2 / (1 + retryProbability p q)) ≤ 1
    rw [← ofReal_mul hr, ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    rw [← mul_div_assoc]
    apply (div_le_one (by linarith : 0 < 1 + retryProbability p q)).2
    dsimp [retryProbability]
    linarith [p.2.1, q.2.1]
  calc
    _ = (ofReal (retryProbability p q) * pmf (bias p q) true +
          ofReal (1 / 2 : ℝ) * pmf p true) * F true +
        (ofReal (retryProbability p q) * pmf (bias p q) false +
          ofReal (1 / 2 : ℝ) * pmf q true) * F false +
        (ofReal (retryProbability p q) * (factor p q : ℝ≥0∞)) * ε := by
      rw [hsplit]
      norm_num [fairCredit, coinCredit, lintegral_law, RealCoin.credit, pmf, VonNeumann.fairBias]
      ring
    _ ≤ _ := by
      rw [htrue, hfalse]
      exact add_le_add le_rfl (mul_le_of_le_one_left' hterm)

end

end SampLib.BernoulliRace
