module

public import SampLib.Distributions.ReverseBinomialJoint

@[expose] public section

/-! # Reverse binomial transport on finite count types -/

open MeasureTheory Finset
open scoped ENNReal

namespace SampLib.ReverseBinomial

noncomputable section

/-- Any count credit can be integrated over the actual finite binomial support. -/
theorem binomial_expectation_fin (n : ℕ) (p : unitInterval) (F : ℕ → ℝ≥0∞) :
    ∫⁻ j, F j ∂ProbabilityTheory.binomial n p =
      ∑ j : Fin (n + 1), ProbabilityTheory.binomial n p {(j : ℕ)} * F j := by
  conv_lhs => rw [ProbabilityTheory.binomial_eq_sum_dirac]
  simp only [lintegral_finsetSum_measure, lintegral_smul_measure, smul_eq_mul,
    lintegral_dirac' _ (measurable_of_countable F)]
  rw [← Nat.range_succ_eq_Iic, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro j _
  rw [ProbabilityTheory.binomial_singleton]

/-- The reverse kernel sums over the finite type of previous counts. -/
theorem kernel_expectation_fin (n m k : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ j, F j ∂kernel n m k = ∑ j : Fin (n + 1), weight n m k j * F j := by
  rw [expectation_degree, ← Fin.sum_univ_eq_sum_range]

/-- The total of a valid previous count and a valid independent increment. -/
def totalCount {n m : ℕ} (hnm : n ≤ m) (j : Fin (n + 1)) (d : Fin (m - n + 1)) :
    Fin (m + 1) :=
  ⟨(j : ℕ) + d, Nat.lt_succ_of_le
    ((Nat.add_le_add (Nat.le_of_lt_succ j.isLt) (Nat.le_of_lt_succ d.isLt)).trans
      (Nat.add_sub_of_le hnm).le)⟩

/-- Exact finite-history transport, without any bound on the joint credit. -/
theorem expectation_joint_fin (n m : ℕ) (hnm : n ≤ m) (p : unitInterval)
    (G : Fin (n + 1) → Fin (m + 1) → ℝ≥0∞) :
    (∑ j : Fin (n + 1), ProbabilityTheory.binomial n p {(j : ℕ)} *
      ∑ d : Fin (m - n + 1), ProbabilityTheory.binomial (m - n) p {(d : ℕ)} *
        G j (totalCount hnm j d)) =
      ∑ k : Fin (m + 1), ProbabilityTheory.binomial m p {(k : ℕ)} *
        ∑ j : Fin (n + 1), weight n m k j * G j k := by
  let extend (j k : ℕ) : ℝ≥0∞ :=
    if hj : j < n + 1 then if hk : k < m + 1 then G ⟨j, hj⟩ ⟨k, hk⟩ else 0 else 0
  have h := expectation_joint n m hnm p extend
  simp_rw [binomial_expectation_fin, kernel_expectation_fin] at h
  have hleft (j : Fin (n + 1)) (d : Fin (m - n + 1)) :
      extend j ((j : ℕ) + d) = G j (totalCount hnm j d) := by
    have hbound : (j : ℕ) + d < m + 1 := (totalCount hnm j d).isLt
    simp only [extend, dite_eq_left j.isLt, dite_eq_left hbound]
    rfl
  have hright (j : Fin (n + 1)) (k : Fin (m + 1)) : extend j k = G j k := by
    simp only [extend, dite_eq_left j.isLt, dite_eq_left k.isLt]
  simpa only [hleft, hright] using h

end

end SampLib.ReverseBinomial
