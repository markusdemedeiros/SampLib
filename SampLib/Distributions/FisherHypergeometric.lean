import SampLib.Samplers.WeightedChoice
import SampLib.Distributions.FisherWeights

/-! # Fisher's noncentral hypergeometric law

Conditioning independent binomial counts on their sum leaves weights proportional
to `choose ones k * choose zeros (n-k) * a^k * b^(n-k)` for odds `a/b`.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.FisherHypergeometric

noncomputable section

/-- The normalized finite Fisher weights; invalid inputs have a total zero-count extension. -/
def law (n ones zeros a b : ℕ) : Measure ℕ :=
  if 0 < (table n ones zeros a b).sum then WeightedChoice.law (table n ones zeros a b)
  else Measure.dirac 0

instance (n ones zeros a b : ℕ) : IsProbabilityMeasure (law n ones zeros a b) := by
  unfold law
  split
  next h =>
    let _ : NeZero (table n ones zeros a b).sum := ⟨Nat.ne_of_gt h⟩
    infer_instance
  next => infer_instance

/-- The standard finite Fisher probability mass function. -/
theorem law_singleton (n ones zeros a b k : ℕ) (hn : n ≤ ones + zeros)
    (ha : 0 < a) (hb : 0 < b) :
    law n ones zeros a b {k} =
      (if k ≤ n then (weight n ones zeros a b k : ℝ≥0∞) else 0) /
        (table n ones zeros a b).sum := by
  rw [law, ite_eq_left (total_pos n ones zeros a b hn ha hb),
    WeightedChoice.law_singleton, table_get]
  split <;> simp

end

end SampLib.FisherHypergeometric
