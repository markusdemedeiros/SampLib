import SampLib.Common.Laws.AlternatingFactorial
import SampLib.Bernoulli.Laws.CoinProduct
import SampLib.Continuous.Laws.IterateCoin

/-! # Laws of the rational negative-exponential coin

The integer part of `a/b` is a product of independent `exp(-1)` trials. On the fractional
part, the parity of the first failed factorial trial gives `exp(-t)`; from the second trial
on, at most half the mass continues, so doubling the retry credit funds termination.
-/

open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.ExpMinusRational

noncomputable section

/-- The negative exponential of a nonnegative rational. -/
def bias (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) : unitInterval :=
  ⟨Real.exp (-(a : ℝ) / b), (Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast neg_nonpos.mpr ha)
      (by exact_mod_cast hb.le))⟩

/-- Integer and fractional parts factor the rational exponential. -/
theorem split_bias (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) :
    IterateCoin.bias (bias 1 1 (by decide) (by decide)) (a / b).toNat *
      bias (a % b) b (Int.emod_nonneg _ hb.ne') hb = bias a b ha hb := by
  apply Subtype.ext
  simp only [Set.Icc.coe_mul, IterateCoin.bias, bias, Int.cast_one, div_one]
  change Real.exp (-1) ^ (a / b).toNat * Real.exp (-(a % b : ℤ) / (b : ℝ)) =
    Real.exp (-(a : ℝ) / b)
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  have hq : 0 ≤ a / b := Int.ediv_nonneg ha hb.le
  have hqcast : ((a / b).toNat : ℝ) = ((a / b : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hq
  have hsplit : (b : ℝ) * (a / b : ℤ) + (a % b : ℤ) = a := by
    exact_mod_cast Int.mul_ediv_add_emod a b
  rw [hqcast]
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  field_simp
  nlinarith

def outerCredit (a b : ℤ) (_ha : 0 ≤ a) (hb : 0 < b)
    (F : Bool → ℝ≥0∞) : Bool → ℝ≥0∞ :=
  CoinProduct.firstCredit (bias (a % b) b (Int.emod_nonneg _ hb.ne') hb) F

theorem outer_expectation (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b)
    (F : Bool → ℝ≥0∞) :
    IterateCoin.credit (bias 1 1 (by decide) (by decide)) (a / b).toNat
      (outerCredit a b ha hb F) = RealCoin.credit (bias a b ha hb) F := by
  rw [IterateCoin.credit, ← RealCoin.lintegral_law, outerCredit]
  rw [CoinProduct.expectation_preservation, CoinProduct.law, split_bias]
  rw [RealCoin.lintegral_law]

def trialBias (t : unitInterval) (i : ℕ) (hi : 1 ≤ i) : unitInterval :=
  ⟨(t : ℝ) / i, div_nonneg t.2.1 (Nat.cast_nonneg _), by
    have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
    exact (div_le_one (by positivity)).mpr (t.2.2.trans hiR)⟩

def coinCredit (t : unitInterval) (i : ℕ) (F : Bool → ℝ≥0∞)
    (b : Bool) (ε : ℝ≥0∞) (r : Bool) : ℝ≥0∞ :=
  if r then AlternatingFactorial.credit t (i + 1) F (!b) + 2 * ε else F b

/-- The factorial recurrence preserves distribution credit; from step two, at
most half the probability continues, so doubling funds termination. -/
theorem expectation (t : unitInterval) (i : ℕ) (hi : 2 ≤ i)
    (F : Bool → ℝ≥0∞) (b : Bool) (ε : ℝ≥0∞) :
    RealCoin.credit (trialBias t i (by omega)) (coinCredit t i F b ε) ≤
      AlternatingFactorial.credit t i F b + ε := by
  have hq : ofReal ((t : ℝ) / i) * 2 ≤ 1 := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (div_nonneg t.2.1 (Nat.cast_nonneg _))]
    apply ENNReal.ofReal_le_one.mpr
    have hiR : (2 : ℝ) ≤ i := by exact_mod_cast hi
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < i)).mpr
    nlinarith [t.2.2]
  rw [AlternatingFactorial.credit_step]
  simp only [RealCoin.credit, RealCoin.pmf, trialBias, coinCredit,
    Bool.false_eq_true, ite_true, ite_false, AlternatingFactorial.hazard]
  calc
    _ = ofReal (1 - (t : ℝ) / i) * F b +
        ofReal ((t : ℝ) / i) * AlternatingFactorial.credit t (i + 1) F (!b) +
        (ofReal ((t : ℝ) / i) * 2) * ε := by ring
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_left' hq)

theorem first_expectation (t : unitInterval) (i : ℕ) (hi : 1 ≤ i)
    (F : Bool → ℝ≥0∞) (b : Bool) :
    RealCoin.credit (trialBias t i hi) (coinCredit t i F b 0) =
      AlternatingFactorial.credit t i F b := by
  rw [AlternatingFactorial.credit_step]
  simp [RealCoin.credit, RealCoin.pmf, trialBias, coinCredit,
    AlternatingFactorial.hazard, add_comm]

end

end SampLib.ExpMinusRational
