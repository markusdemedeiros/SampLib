module

public import SampLib.Bernoulli.Laws.ReverseBinomial

@[expose] public section

/-! # Joint-credit disintegration of split binomial counts

The hypergeometric coefficient cancels only the positive combinatorial
normalizer. Neither Bernoulli probability is divided, preserving endpoint biases
and infinite continuation credits.
-/

open Set MeasureTheory
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.ReverseBinomial

noncomputable section

private theorem binomial_mass (n j : ℕ) (p : unitInterval) :
    ProbabilityTheory.binomial n p {j} =
      (n.choose j : ℝ≥0∞) * ofReal (p : ℝ) ^ j * ofReal (1 - (p : ℝ)) ^ (n - j) := by
  rw [ProbabilityTheory.binomial_singleton,
    ENNReal.ofReal_mul (mul_nonneg (by positivity) (pow_nonneg p.2.1 _)),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow p.2.1, ENNReal.ofReal_pow (sub_nonneg.mpr p.2.2)]

/-- Splitting a fixed total factors its joint mass into binomial and hypergeometric parts. -/
theorem mass_factorization (n m j d : ℕ) (hnm : n ≤ m) (p : unitInterval) :
    ProbabilityTheory.binomial n p {j} * ProbabilityTheory.binomial (m - n) p {d} =
      ProbabilityTheory.binomial m p {j + d} * weight n m (j + d) j := by
  by_cases hj : j ≤ n
  · by_cases hd : d ≤ m - n
    · have hk : j + d ≤ m := by omega
      have hc : (m.choose (j + d) : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos hk).ne'
      have he : n - j + (m - n - d) = m - (j + d) := by omega
      rw [binomial_mass, binomial_mass, binomial_mass, weight_eq_div n m (j + d) j hk,
        numerator_of_le n m (j + d) j (by omega), Nat.add_sub_cancel_left, Nat.cast_mul]
      calc
        _ = ((n.choose j : ℝ≥0∞) * (m - n).choose d) *
            (ofReal (p : ℝ) ^ (j + d) * ofReal (1 - (p : ℝ)) ^ (m - (j + d))) := by
          rw [pow_add, ← he, pow_add]
          ring
        _ = ((m.choose (j + d) : ℝ≥0∞) *
            (((n.choose j : ℝ≥0∞) * (m - n).choose d) / m.choose (j + d))) *
            (ofReal (p : ℝ) ^ (j + d) * ofReal (1 - (p : ℝ)) ^ (m - (j + d))) := by
          rw [ENNReal.mul_div_cancel hc (by simp)]
        _ = _ := by rw [div_eq_mul_inv]; ring
    · have hd' : m - n < d := by omega
      simp [binomial_mass, Nat.choose_eq_zero_of_lt hd', weight, coefficient,
        numerator_of_le n m (j + d) j (by omega)]
  · have hj' : n < j := by omega
    simp [binomial_mass, Nat.choose_eq_zero_of_lt hj', weight, coefficient, numerator, hj]

/-- The total count followed by its conditional previous count. -/
def joint (n m : ℕ) (p : unitInterval) : Measure (ℕ × ℕ) :=
  (ProbabilityTheory.binomial m p).bind
    (fun k => (kernel n m k).map (fun j => (j, k)))

private theorem tagged_singleton (n m t j k : ℕ) :
    ((kernel n m t).map (fun a => (a, t))) {(j, k)} =
      if t = k then weight n m k j else 0 := by
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  by_cases ht : t = k
  · subst t
    have hs : (fun a : ℕ => (a, k)) ⁻¹' {(j, k)} = {j} := by ext a; simp
    rw [hs, kernel_singleton, ite_eq_left rfl]
  · have hs : (fun a : ℕ => (a, t)) ⁻¹' {(j, k)} = ∅ := by
      ext a
      simp [ht]
    simp [hs, ht]

theorem joint_singleton (n m j k : ℕ) (p : unitInterval) :
    joint n m p {(j, k)} = ProbabilityTheory.binomial m p {k} * weight n m k j := by
  rw [joint, Measure.bind_apply (measurableSet_singleton _)
    (measurable_of_countable _).aemeasurable]
  simp_rw [tagged_singleton]
  have hf : (fun t : ℕ => if t = k then weight n m k j else 0) =
      ({k} : Set ℕ).indicator (fun _ => weight n m k j) := by
    ext t
    by_cases h : t = k <;> simp [h]
  rw [hf, lintegral_indicator (measurableSet_singleton _), setLIntegral_const, mul_comm]

/-- The split trials and reverse conditional law are the same joint distribution. -/
theorem joint_eq (n m : ℕ) (hnm : n ≤ m) (p : unitInterval) :
    ((ProbabilityTheory.binomial n p).prod (ProbabilityTheory.binomial (m - n) p)).map
      (fun z : ℕ × ℕ => (z.1, z.1 + z.2)) = joint n m p := by
  apply Measure.ext_of_singleton
  rintro ⟨j, k⟩
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _), joint_singleton]
  by_cases hj : j ≤ k
  · have hs : (fun z : ℕ × ℕ => (z.1, z.1 + z.2)) ⁻¹' {(j, k)} = {(j, k - j)} := by
      ext ⟨a, d⟩
      simp only [mem_preimage, mem_singleton_iff, Prod.mk.injEq]
      omega
    rw [hs, ← singleton_prod_singleton, Measure.prod_prod,
      mass_factorization n m j (k - j) hnm p, Nat.add_sub_of_le hj]
  · have hs : (fun z : ℕ × ℕ => (z.1, z.1 + z.2)) ⁻¹' {(j, k)} = ∅ := by
      ext ⟨a, d⟩
      simp only [mem_preimage, mem_singleton_iff, Prod.mk.injEq, mem_empty_iff_false, iff_false]
      omega
    rw [hs, measure_empty, weight_eq_zero_of_lt n m k j (by omega), mul_zero]

/-- Disintegrate every joint continuation credit, including infinite credits. -/
theorem expectation_joint (n m : ℕ) (hnm : n ≤ m) (p : unitInterval)
    (G : ℕ → ℕ → ℝ≥0∞) :
    ∫⁻ j, (∫⁻ d, G j (j + d) ∂ProbabilityTheory.binomial (m - n) p)
        ∂ProbabilityTheory.binomial n p =
      ∫⁻ k, (∫⁻ j, G j k ∂kernel n m k) ∂ProbabilityTheory.binomial m p := by
  calc
    _ = ∫⁻ z : ℕ × ℕ, G z.1 (z.1 + z.2)
        ∂(ProbabilityTheory.binomial n p).prod (ProbabilityTheory.binomial (m - n) p) :=
      (lintegral_prod _ (measurable_of_countable _).aemeasurable).symm
    _ = ∫⁻ z : ℕ × ℕ, G z.1 z.2
        ∂((ProbabilityTheory.binomial n p).prod (ProbabilityTheory.binomial (m - n) p)).map
          (fun z : ℕ × ℕ => (z.1, z.1 + z.2)) := by
      rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
    _ = _ := by
      rw [joint_eq n m hnm p, joint,
        Measure.lintegral_bind (measurable_of_countable _).aemeasurable
          (measurable_of_countable _).aemeasurable]
      congr 1
      funext k
      rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

/-- The conditional expectation may be summed over the previous trial count instead. -/
theorem expectation_degree (n m k : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ j, F j ∂kernel n m k =
      ∑ j ∈ Finset.range (n + 1), weight n m k j * F j := by
  rw [expectation]
  rcases le_total k n with h | h
  · apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right h 1))
    intro j _ hj
    rw [weight_eq_zero_of_lt n m k j (by simpa using hj), zero_mul]
  · symm
    apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right h 1))
    intro j _ hj
    rw [weight_coefficient, coefficient_zero_of_lt_degree n m k j (by simpa using hj)]
    simp

/-- Finite-history form of the joint transport; no finiteness condition on `G` is needed. -/
theorem expectation_joint_sum (n m : ℕ) (hnm : n ≤ m) (p : unitInterval)
    (G : ℕ → ℕ → ℝ≥0∞) :
    ∫⁻ j, (∫⁻ d, G j (j + d) ∂ProbabilityTheory.binomial (m - n) p)
        ∂ProbabilityTheory.binomial n p =
      ∫⁻ k, (∑ j ∈ Finset.range (n + 1), weight n m k j * G j k)
        ∂ProbabilityTheory.binomial m p := by
  rw [expectation_joint n m hnm p G]
  simp_rw [expectation_degree]

end

end SampLib.ReverseBinomial
