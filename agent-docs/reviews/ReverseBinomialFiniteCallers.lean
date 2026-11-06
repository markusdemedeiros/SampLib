import SampLib.Distributions.ReverseBinomialFinite

open MeasureTheory SampLib.ReverseBinomial
open scoped ENNReal

example (n m : ℕ) (hnm : n ≤ m) (p : unitInterval)
    (G : Fin (n + 1) → Fin (m + 1) → ℝ≥0∞) :
    (∑ j : Fin (n + 1), ProbabilityTheory.binomial n p {(j : ℕ)} *
      ∑ d : Fin (m - n + 1), ProbabilityTheory.binomial (m - n) p {(d : ℕ)} *
        G j ⟨(j : ℕ) + d, by omega⟩) =
      ∑ k : Fin (m + 1), ProbabilityTheory.binomial m p {(k : ℕ)} *
        ∑ j : Fin (n + 1), weight n m k j * G j k :=
  expectation_joint_fin n m hnm p G

example (n m : ℕ) (hnm : n ≤ m) :=
  expectation_joint_fin n m hnm 0 (fun j k => if j = 0 ∧ k = 0 then ∞ else 0)

example (n m : ℕ) (hnm : n ≤ m) :=
  expectation_joint_fin n m hnm 1 (fun j k => if (j : ℕ) = n ∧ (k : ℕ) = m then ∞ else 0)

example (m : ℕ) (p : unitInterval) (G : Fin 1 → Fin (m + 1) → ℝ≥0∞) :=
  expectation_joint_fin 0 m (Nat.zero_le m) p G

example (m : ℕ) (p : unitInterval) (G : Fin (m + 1) → Fin (m + 1) → ℝ≥0∞) :=
  expectation_joint_fin m m le_rfl p G

example (p : unitInterval) := expectation_joint_fin 0 0 le_rfl p (fun _ _ => ∞)

#print axioms expectation_joint_fin
#print axioms binomial_expectation_fin
#print axioms kernel_expectation_fin
