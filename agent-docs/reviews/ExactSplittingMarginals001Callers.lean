import SampLib.Weighted.Laws.SplittingPPSMarginals

open scoped ENNReal

namespace ReviewExactSplittingMarginals001

noncomputable section

open SampLib.SplittingPPS

example (amount cutoff : ℕ) (items : List Item)
    (h : ∀ a ∈ items.drop cutoff, amount ≤ a.1) (G : ℤ → ℝ≥0∞) :=
  numeratorCredit_split amount cutoff items h G

example (amount cutoff denominator : ℕ) (items : List Item)
    (h : ∀ a ∈ items.drop cutoff, amount ≤ a.1) (hd : amount < denominator)
    (G : ℤ → ℝ≥0∞) :=
  inclusion_credit_expectation amount cutoff denominator items h hd G

/-- A zero inclusion numerator annihilates even infinite continuation credit. -/
example : numeratorCredit [(0, 0), (1, 1)] (fun label => if label = 0 then ∞ else 1) = 1 := by
  simp [numeratorCredit]

/-- A zero split remains valid when its selected-block sum is infinite. -/
example (G : ℤ → ℝ≥0∞) :=
  inclusion_credit_expectation 0 0 2 [(0, 0), (1, 1)]
    (fun _ _ => Nat.zero_le _) (by decide) G

private theorem capacity : ∀ a ∈ ([(0, 0), (2, 1)] : List Item).drop 1, 1 ≤ a.1 := by
  simp

/-- Residual normalization uses a positive finite denominator, never infinity subtraction. -/
example := inclusion_credit_expectation 1 1 3 [(0, 0), (2, 1)] capacity (by decide)
  (fun label => if label = 0 then ∞ else 2)

#print axioms SampLib.SplittingPPS.numeratorCredit_split
#print axioms SampLib.SplittingPPS.inclusion_credit_expectation

end

end ReviewExactSplittingMarginals001
