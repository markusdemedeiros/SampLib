import SampLib.Bernoulli.Laws.ReverseBinomialJoint

open MeasureTheory SampLib.ReverseBinomial
open scoped ENNReal

example (n m : ℕ) (hnm : n ≤ m) (p : unitInterval) (G : ℕ → ℕ → ℝ≥0∞) :
    ∫⁻ j, (∫⁻ d, G j (j + d) ∂ProbabilityTheory.binomial (m - n) p)
        ∂ProbabilityTheory.binomial n p =
      ∫⁻ k, (∑ j ∈ Finset.range (n + 1), weight n m k j * G j k)
        ∂ProbabilityTheory.binomial m p := expectation_joint_sum n m hnm p G

example (n m : ℕ) (hnm : n ≤ m) :
    ∫⁻ j, (∫⁻ d, (if j = 0 ∧ j + d = 0 then ∞ else 0)
        ∂ProbabilityTheory.binomial (m - n) 0) ∂ProbabilityTheory.binomial n 0 =
      ∫⁻ k, (∫⁻ j, (if j = 0 ∧ k = 0 then ∞ else 0) ∂kernel n m k)
        ∂ProbabilityTheory.binomial m 0 :=
  expectation_joint n m hnm 0 (fun j k => if j = 0 ∧ k = 0 then ∞ else 0)

example (n m : ℕ) (hnm : n ≤ m) :
    ∫⁻ j, (∫⁻ d, (if j = n ∧ j + d = m then ∞ else 0)
        ∂ProbabilityTheory.binomial (m - n) 1) ∂ProbabilityTheory.binomial n 1 =
      ∫⁻ k, (∫⁻ j, (if j = n ∧ k = m then ∞ else 0) ∂kernel n m k)
        ∂ProbabilityTheory.binomial m 1 :=
  expectation_joint n m hnm 1 (fun j k => if j = n ∧ k = m then ∞ else 0)

example (m : ℕ) (p : unitInterval) (G : ℕ → ℕ → ℝ≥0∞) :=
  expectation_joint 0 m (Nat.zero_le m) p G

example (m : ℕ) (p : unitInterval) (G : ℕ → ℕ → ℝ≥0∞) :=
  expectation_joint m m le_rfl p G

example (p : unitInterval) (G : ℕ → ℕ → ℝ≥0∞) :=
  expectation_joint 0 0 le_rfl p G

example (p : unitInterval) :
    ProbabilityTheory.binomial 2 p {1} * ProbabilityTheory.binomial 3 p {2} =
      ProbabilityTheory.binomial 5 p {3} * weight 2 5 3 1 :=
  mass_factorization 2 5 1 2 (by omega) p

example (n m : ℕ) (hnm : n ≤ m) (p : unitInterval) := joint_eq n m hnm p

#print axioms mass_factorization
#print axioms joint_eq
#print axioms expectation_joint
#print axioms expectation_degree
#print axioms expectation_joint_sum
