import SampLib.Uniform.Laws.RationalCoin

/-! # Bernoulli thresholds on a uniform integer rank -/

open scoped ENNReal

namespace SampLib.IntegerThreshold

noncomputable section

/-- The fraction of ranks below the threshold. -/
abbrev bias (a b : ℕ) (hb : 0 < b) (hab : a ≤ b) : unitInterval :=
  RationalCoin.bias a b (by positivity) (by exact_mod_cast hb) (by exact_mod_cast hab)

/-- Counting the accepted ranks gives the rational Bernoulli expectation. -/
theorem expectation (a b : ℕ) (hb : 0 < b) (hab : a ≤ b) (F : Bool → ℝ≥0∞) :
    (∑ k ∈ Finset.range b, RationalCoin.rankCredit a F k) / b =
      RealCoin.credit (bias a b hb hab) F := by
  simpa using RationalCoin.expectation (a : ℤ) (b : ℤ) (by positivity)
    (by exact_mod_cast hb) (by exact_mod_cast hab) F

theorem rankCredit_eq (a : ℕ) (F : Bool → ℝ≥0∞) (k : ℕ) :
    RationalCoin.rankCredit a F k = F (decide ((k : ℤ) < (a : ℤ))) := by
  by_cases h : (k : ℤ) < (a : ℤ) <;> simp [RationalCoin.rankCredit, h]

end

end SampLib.IntegerThreshold
