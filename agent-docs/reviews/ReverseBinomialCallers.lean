import SampLib.Distributions.ReverseBinomial

open MeasureTheory SampLib.ReverseBinomial
open scoped ENNReal

example (n m k : ℕ) (hnm : n ≤ m) (hkm : k ≤ m) :
    ∑ j ∈ Finset.range (n + 1), (coefficient n m k j : ℝ) = 1 :=
  coefficient_sum_degree_real n m k hnm hkm

example (n m k : ℕ) (hnm : n ≤ m) (hkm : k ≤ m) :
    IsProbabilityMeasure (law n m k hnm hkm) := inferInstance

example : coefficient 2 5 3 1 = 3 / 5 := by norm_num [coefficient, numerator, Nat.choose]
example : coefficient 2 5 3 4 = 0 := by norm_num [coefficient, numerator]
example : coefficient 2 5 3 3 = 0 := by norm_num [coefficient, numerator]
example : coefficient 4 5 4 1 = 0 := by norm_num [coefficient, numerator, Nat.choose]
example : coefficient 0 0 0 0 = 1 := by norm_num [coefficient, numerator]
example : coefficient 3 3 2 2 = 1 := by norm_num [coefficient, numerator, Nat.choose]

example (m k : ℕ) (hk : k ≤ m) : kernel 0 m k = Measure.dirac 0 := kernel_zero_left m k hk

example (n m k j : ℕ) (hkm : k ≤ m) (hjk : j ≤ k) (hjn : j ≤ n)
    (hrest : k - j ≤ m - n) : 0 < coefficient n m k j :=
  coefficient_pos n m k j hkm hjk hjn hrest

example (n m k : ℕ) :
    ∫⁻ j, (if j = 0 then ∞ else 0) ∂kernel n m k =
      ∑ j ∈ Finset.range (k + 1), weight n m k j * (if j = 0 then ∞ else 0) :=
  expectation n m k _

#print axioms coefficient_sum
#print axioms coefficient_sum_degree
#print axioms coefficient_pos
#print axioms weight_sum
#print axioms kernel_zero_left
#print axioms expectation
