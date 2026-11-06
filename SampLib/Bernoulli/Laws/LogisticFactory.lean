import SampLib.Uniform.Laws.RealCoin

/-! # Laws of the logistic Bernoulli factory

A selector returns `false` with probability `r`; otherwise the input coin decides. The
success bias is `(1-r)p / (r + (1-r)p)`, which equals `xp/(y+xp)` when `r = y/(x+y)`.
Each retry amplifies the remaining credit by `1/(1-r)`, which pays for termination.
-/

open ENNReal (ofReal ofReal_add ofReal_mul)
open scoped ENNReal NNReal

namespace SampLib.LogisticFactory

open RealCoin (pmf lintegral_law)

noncomputable section

section distribution

private theorem denominator_pos (p r : unitInterval) (hr : 0 < (r : ℝ)) :
    0 < (r : ℝ) + (1 - (r : ℝ)) * (p : ℝ) :=
  add_pos_of_pos_of_nonneg hr (mul_nonneg (sub_nonneg.mpr r.2.2) p.2.1)

/-- Normalized probability of an accepted input success. -/
def bias (p r : unitInterval) (hr : 0 < (r : ℝ)) : unitInterval :=
  ⟨((1 - (r : ℝ)) * (p : ℝ)) / ((r : ℝ) + (1 - (r : ℝ)) * (p : ℝ)),
    div_nonneg (mul_nonneg (sub_nonneg.mpr r.2.2) p.2.1) (denominator_pos p r hr).le,
    (div_le_one (denominator_pos p r hr)).mpr (le_add_of_nonneg_left r.2.1)⟩

abbrev law (p r : unitInterval) (hr : 0 < (r : ℝ)) := RealCoin.law (bias p r hr)
abbrev credit (p r : unitInterval) (hr : 0 < (r : ℝ)) := RealCoin.credit (bias p r hr)

end distribution

section termination

private def retryProbability (p r : unitInterval) : ℝ := (1 - (r : ℝ)) * (1 - (p : ℝ))

/-- A continued selector amplifies credit by its inverse probability. -/
def terminationFactor (r : unitInterval) : ℝ≥0 :=
  ⟨1 / (1 - (r : ℝ)), div_nonneg zero_le_one (sub_nonneg.mpr r.2.2)⟩

theorem one_lt_terminationFactor (r : unitInterval) (hr : 0 < (r : ℝ))
    (hr1 : (r : ℝ) < 1) : 1 < terminationFactor r := by
  exact_mod_cast (one_lt_div (sub_pos.mpr hr1)).mpr (by linarith : 1 - (r : ℝ) < 1)

end termination

section conservation

/-- Credit assigned to the input result after the selector continues. -/
def inputCredit (p r : unitInterval) (hr : 0 < (r : ℝ))
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F true else credit p r hr F + terminationFactor r * ε

/-- Conditional credit after the selector. -/
def selectorCredit (p r : unitInterval) (hr : 0 < (r : ℝ))
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F false else ∫⁻ a, inputCredit p r hr F ε a ∂RealCoin.law p

/-- The selector/input recurrence preserves the logistic bias and funds retries. -/
theorem expectation_preservation (p r : unitInterval) (hr : 0 < (r : ℝ))
    (hr1 : (r : ℝ) < 1) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ b, selectorCredit p r hr F ε b ∂RealCoin.law r ≤ credit p r hr F + ε := by
  have hp := p.2.1
  have hpc := sub_nonneg.mpr p.2.2
  have hrc := sub_nonneg.mpr r.2.2
  have hq : 0 ≤ retryProbability p r := mul_nonneg hrc hpc
  have hbalance : retryProbability p r + ((r : ℝ) + (1 - (r : ℝ)) * (p : ℝ)) = 1 := by
    dsimp [retryProbability]
    ring
  have ht := (bias p r hr).2.1
  have hf := sub_nonneg.mpr (bias p r hr).2.2
  have hsplit : ofReal (retryProbability p r) = pmf r false * pmf p false := by
    change ofReal ((1 - (r : ℝ)) * (1 - (p : ℝ))) =
      ofReal (1 - (r : ℝ)) * ofReal (1 - (p : ℝ))
    exact ofReal_mul hrc
  have htrue : ofReal (retryProbability p r) * pmf (bias p r hr) true +
      pmf r false * pmf p true = pmf (bias p r hr) true := by
    change ofReal (retryProbability p r) * ofReal (bias p r hr : ℝ) +
      ofReal (1 - (r : ℝ)) * ofReal (p : ℝ) = ofReal (bias p r hr : ℝ)
    rw [← ofReal_mul hq, ← ofReal_mul hrc,
      ← ofReal_add (mul_nonneg hq ht) (mul_nonneg hrc hp)]
    congr 1
    dsimp [bias]
    field_simp [(denominator_pos p r hr).ne']
    linear_combination (p : ℝ) * hbalance
  have hfalse : ofReal (retryProbability p r) * pmf (bias p r hr) false +
      pmf r true = pmf (bias p r hr) false := by
    change ofReal (retryProbability p r) * ofReal (1 - (bias p r hr : ℝ)) +
      ofReal (r : ℝ) = ofReal (1 - (bias p r hr : ℝ))
    rw [← ofReal_mul hq, ← ofReal_add (mul_nonneg hq hf) r.2.1]
    congr 1
    dsimp [bias]
    field_simp [(denominator_pos p r hr).ne']
    linear_combination (r : ℝ) * hbalance
  have hamp : ofReal (retryProbability p r) * (terminationFactor r : ℝ≥0∞) ≤ 1 := by
    rw [ENNReal.coe_nnreal_eq]
    change ofReal (retryProbability p r) * ofReal (1 / (1 - (r : ℝ))) ≤ 1
    rw [← ofReal_mul hq, ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hcancel : retryProbability p r * (1 / (1 - (r : ℝ))) = 1 - (p : ℝ) := by
      dsimp [retryProbability]
      field_simp [(sub_pos.mpr hr1).ne']
    rw [hcancel]
    linarith [p.2.1]
  calc
    _ = (ofReal (retryProbability p r) * pmf (bias p r hr) true +
          pmf r false * pmf p true) * F true +
        (ofReal (retryProbability p r) * pmf (bias p r hr) false + pmf r true) * F false +
        (ofReal (retryProbability p r) * (terminationFactor r : ℝ≥0∞)) * ε := by
      rw [hsplit]
      norm_num [selectorCredit, inputCredit, lintegral_law, RealCoin.credit, credit, pmf]
      ring
    _ ≤ _ := by
      rw [htrue, hfalse]
      exact add_le_add le_rfl (mul_le_of_le_one_left (show 0 ≤ ε from zero_le) hamp)

end conservation

section integerParameters

private theorem integer_denominator_pos (p : unitInterval) (x y : ℤ)
    (hx : 0 < x) (hy : 0 < y) : 0 < (y : ℝ) + (x : ℝ) * (p : ℝ) :=
  add_pos_of_pos_of_nonneg (by exact_mod_cast hy)
    (mul_nonneg (by exact_mod_cast hx.le) p.2.1)

/-- The source's logistic bias `x*p/(y+x*p)`. -/
def integerBias (p : unitInterval) (x y : ℤ) (hx : 0 < x) (hy : 0 < y) : unitInterval :=
  ⟨((x : ℝ) * (p : ℝ)) / ((y : ℝ) + (x : ℝ) * (p : ℝ)),
    div_nonneg (mul_nonneg (by exact_mod_cast hx.le) p.2.1)
      (integer_denominator_pos p x y hx hy).le,
    (div_le_one (integer_denominator_pos p x y hx hy)).mpr
      (le_add_of_nonneg_left (by exact_mod_cast hy.le))⟩

theorem selector_parameters (p : unitInterval) (x y : ℤ) (hx : 0 < x) (hy : 0 < y)
    (r : unitInterval) (hratio : (r : ℝ) = (y : ℝ) / ((x + y : ℤ) : ℝ)) :
    ∃ hr : 0 < (r : ℝ), (r : ℝ) < 1 ∧ bias p r hr = integerBias p x y hx hy := by
  have hxy : 0 < ((x + y : ℤ) : ℝ) := by exact_mod_cast (show 0 < x + y by omega)
  have hr : 0 < (r : ℝ) := by rw [hratio]; exact div_pos (by exact_mod_cast hy) hxy
  have hr1 : (r : ℝ) < 1 := by
    rw [hratio]
    exact (div_lt_one hxy).mpr (by exact_mod_cast (show y < x + y by omega))
  refine ⟨hr, hr1, ?_⟩
  have hd := denominator_pos p r hr
  apply Subtype.ext
  change ((1 - (r : ℝ)) * (p : ℝ)) / ((r : ℝ) + (1 - (r : ℝ)) * (p : ℝ)) = _
  rw [hratio] at hd ⊢
  dsimp [integerBias]
  push_cast at hxy hd ⊢
  field_simp [hxy.ne', hd.ne', (integer_denominator_pos p x y hx hy).ne']
  ring

end integerParameters

end

end SampLib.LogisticFactory
