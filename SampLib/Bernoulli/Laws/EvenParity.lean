import SampLib.Uniform.Laws.RealCoin

/-! # Laws of the even-parity factory

A pair of successes retries, so the output bias is `1/(1+p)`. Each retry amplifies the
remaining credit by `factor p`, which pays for termination when `p < 1`.
-/

open ENNReal (ofReal ofReal_add ofReal_mul ofReal_pow coe_nnreal_eq)
open scoped ENNReal NNReal

namespace SampLib.EvenParity

open RealCoin (pmf lintegral_law)

noncomputable section

/-- The target bias, including the deterministic `p = 0` case. -/
def bias (p : unitInterval) : unitInterval :=
  ⟨1 / (1 + (p : ℝ)),
    (one_div_pos.mpr (by linarith [p.2.1] : 0 < 1 + (p : ℝ))).le,
    (div_le_one (by linarith [p.2.1] : 0 < 1 + (p : ℝ))).2 (by linarith [p.2.1])⟩

abbrev law (p : unitInterval) := RealCoin.law (bias p)

def credit (p : unitInterval) (F : Bool → ℝ≥0∞) := RealCoin.credit (bias p) F

section termination

def factor (p : unitInterval) : ℝ≥0 :=
  ⟨2 / (1 + (p : ℝ) ^ 2), by positivity⟩

theorem one_lt_factor (p : unitInterval) (hp : (p : ℝ) < 1) : 1 < factor p := by
  have hden : 0 < 1 + (p : ℝ) ^ 2 := by positivity
  have hlt : (p : ℝ) ^ 2 < 1 := by nlinarith [p.2.1]
  exact_mod_cast (one_lt_div hden).2 (by linarith : 1 + (p : ℝ) ^ 2 < 2)

end termination

def pairCredit (p : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (a b : Bool) : ℝ≥0∞ :=
  if a then if b then credit p F + factor p * ε else F false else F true

def firstCredit (p : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (a : Bool) : ℝ≥0∞ :=
  if a then ∫⁻ b, pairCredit p F ε true b ∂RealCoin.law p else F true

/-- Pairing successes preserves the target expectation; retry amplification costs at most `ε`. -/
theorem expectation (p : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ a, firstCredit p F ε a ∂RealCoin.law p ≤ credit p F + ε := by
  have hp0 := p.2.1
  have hp1 := sub_nonneg.mpr p.2.2
  have ht := (bias p).2.1
  have hf := sub_nonneg.mpr (bias p).2.2
  have htrue : ofReal ((p : ℝ) ^ 2) * pmf (bias p) true + pmf p false =
      pmf (bias p) true := by
    simp only [pmf, ite_true, Bool.false_eq_true, ite_false]
    rw [← ofReal_mul (sq_nonneg _), ← ofReal_add (mul_nonneg (sq_nonneg _) ht) hp1]
    congr 1
    dsimp [bias]
    field_simp
    ring
  have hfalse : ofReal ((p : ℝ) ^ 2) * pmf (bias p) false +
      pmf p true * pmf p false = pmf (bias p) false := by
    simp only [pmf, ite_true, Bool.false_eq_true, ite_false]
    rw [← ofReal_mul (sq_nonneg _), ← ofReal_mul hp0,
      ← ofReal_add (mul_nonneg (sq_nonneg _) hf) (mul_nonneg hp0 hp1)]
    congr 1
    dsimp [bias]
    field_simp
    ring
  have hterm : ofReal ((p : ℝ) ^ 2) * (factor p : ℝ≥0∞) ≤ 1 := by
    rw [coe_nnreal_eq]
    change ofReal ((p : ℝ) ^ 2) * ofReal (2 / (1 + (p : ℝ) ^ 2)) ≤ 1
    rw [← ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    rw [← mul_div_assoc]
    apply (div_le_one (by positivity : 0 < 1 + (p : ℝ) ^ 2)).2
    nlinarith [p.2.1, p.2.2]
  calc
    _ = (ofReal ((p : ℝ) ^ 2) * pmf (bias p) true + pmf p false) * F true +
        (ofReal ((p : ℝ) ^ 2) * pmf (bias p) false + pmf p true * pmf p false) * F false +
        (ofReal ((p : ℝ) ^ 2) * (factor p : ℝ≥0∞)) * ε := by
      rw [ofReal_pow hp0, pow_two]
      simp [firstCredit, pairCredit, lintegral_law, credit, RealCoin.credit, pmf]
      ring
    _ ≤ _ := by
      rw [htrue, hfalse]
      change _ ≤ (pmf (bias p) true * F true + pmf (bias p) false * F false) + ε
      exact add_le_add le_rfl (mul_le_of_le_one_left' hterm)

end

end SampLib.EvenParity
