import SampLib.Common.Laws.Binomial

open MeasureTheory
open scoped ENNReal

namespace SampLib.BinomialReview

example (n : ℕ) : Binomial.law 0 n {0} = 1 := by
  simp [Binomial.law_singleton, RealCoin.pmf]

example (n : ℕ) : Binomial.law 1 n {n} = 1 := by
  simp [Binomial.law_singleton, RealCoin.pmf]

example (n : ℕ) : (∫⁻ _ : ℕ, (∞ : ℝ≥0∞) ∂Binomial.law 0 n) = ∞ := by
  simp

example (n : ℕ) : (∫⁻ _ : ℕ, (∞ : ℝ≥0∞) ∂Binomial.law 1 n) = ∞ := by
  simp

#print axioms Binomial.law_singleton
#print axioms Binomial.law_eq_binomial
#print axioms Binomial.lintegral_eq_sum

end SampLib.BinomialReview
