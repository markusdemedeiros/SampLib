import SampLib.Common.Laws.Binomial

/-! # Reflection and independent thinning of binomial counts

Reflection exchanges successes and failures. Thinning independently retains each
success, so the two trial probabilities multiply. Both identities hold for
arbitrary nonnegative extended-real continuations, including infinite credits.
-/

open MeasureTheory Measure
open scoped ENNReal

namespace SampLib.Binomial

noncomputable section

private theorem lintegral_succ (p : unitInterval) (n : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, F k ∂law p (n + 1) =
      RealCoin.pmf p true * (∫⁻ k, F (k + 1) ∂law p n) +
        RealCoin.pmf p false * (∫⁻ k, F k ∂law p n) := by
  simp [law, lintegral_map (measurable_of_countable F) (measurable_of_countable Nat.succ),
    smul_eq_mul, Nat.succ_eq_add_one]

/-- The count lies in the finite range of possible successes. -/
theorem support (p : unitInterval) (n : ℕ) : ∀ᵐ k ∂law p n, k ≤ n := by
  induction n with
  | zero => simp [law]
  | succ n IH =>
    rw [law, ae_add_measure_iff]
    constructor
    · apply ae_smul_measure _ (RealCoin.pmf p true)
      apply (ae_map_iff (measurable_of_countable _).aemeasurable
        (Set.to_countable _).measurableSet).2
      filter_upwards [IH] with k hk
      exact Nat.succ_le_succ hk
    · apply ae_smul_measure _ (RealCoin.pmf p false)
      filter_upwards [IH] with k hk
      exact hk.trans (Nat.le_succ n)

/-- Complementing all `n` independent indicators exchanges `p` and `1-p`. -/
theorem reflection (p : unitInterval) (n : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, F (n - k) ∂law p n = ∫⁻ k, F k ∂law (unitInterval.symm p) n := by
  rw [lintegral_eq_sum, lintegral_eq_sum,
    ← Finset.sum_range_reflect (fun k => ENNReal.ofReal
      ((n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)) * F (n - k))]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  simp only [Nat.add_sub_cancel, Nat.choose_symm hkn, Nat.sub_sub_self hkn,
    unitInterval.coe_symm_eq, sub_sub_cancel]
  congr 2
  ring

private theorem pmf_product (p q : unitInterval) :
    RealCoin.pmf (p * q) true = RealCoin.pmf p true * RealCoin.pmf q true ∧
      RealCoin.pmf (p * q) false =
        RealCoin.pmf p true * RealCoin.pmf q false + RealCoin.pmf p false := by
  simp only [RealCoin.pmf, ite_true, Bool.false_eq_true, ite_false, Set.Icc.coe_mul]
  constructor
  · exact ENNReal.ofReal_mul p.2.1
  · rw [← ENNReal.ofReal_mul p.2.1,
      ← ENNReal.ofReal_add (mul_nonneg p.2.1 (sub_nonneg.mpr q.2.2))
        (sub_nonneg.mpr p.2.2)]
    congr 1
    ring

/-- Independently retaining each success with probability `q` multiplies the bias. -/
theorem thinning (p q : unitInterval) (n : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, (∫⁻ j, F j ∂law q k) ∂law p n = ∫⁻ j, F j ∂law (p * q) n := by
  induction n generalizing F with
  | zero => simp [expectation_zero]
  | succ n IH =>
    rw [lintegral_succ]
    simp_rw [lintegral_succ q]
    rw [lintegral_add_left (measurable_of_countable _),
      lintegral_const_mul _ (measurable_of_countable _),
      lintegral_const_mul _ (measurable_of_countable _), IH, IH, lintegral_succ,
      (pmf_product p q).1, (pmf_product p q).2]
    ring

/-- Independently filling each failure with probability `q` complements thinning. -/
theorem filling (p q : unitInterval) (n : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, (∫⁻ j, F (k + j) ∂law q (n - k)) ∂law p n =
      ∫⁻ j, F j ∂law (unitInterval.symm (unitInterval.symm p * unitInterval.symm q)) n := by
  let G : ℕ → ℝ≥0∞ := fun k => ∫⁻ j, F (n - k + j) ∂law q k
  have hfirst : (∫⁻ k, (∫⁻ j, F (k + j) ∂law q (n - k)) ∂law p n) =
      ∫⁻ k, G (n - k) ∂law p n := by
    apply lintegral_congr_ae
    filter_upwards [support p n] with k hk
    simp only [G, Nat.sub_sub_self hk]
  rw [hfirst, reflection]
  have hsecond : (∫⁻ k, G k ∂law (unitInterval.symm p) n) =
      ∫⁻ k, (∫⁻ j, F (n - j) ∂law (unitInterval.symm q) k)
        ∂law (unitInterval.symm p) n := by
    apply lintegral_congr_ae
    filter_upwards [support (unitInterval.symm p) n] with k hk
    rw [← reflection q k (fun j => F (n - j))]
    apply lintegral_congr_ae
    filter_upwards [support q k] with j hj
    congr 1
    omega
  rw [hsecond, thinning, reflection]

/-- The mean of the independent indicator count is `n p`. -/
theorem mean (p : unitInterval) (n : ℕ) :
    ∫⁻ k, (k : ℝ≥0∞) ∂law p n = n * ENNReal.ofReal (p : ℝ) := by
  induction n with
  | zero => simp [expectation_zero]
  | succ n IH =>
    rw [lintegral_succ]
    simp_rw [Nat.cast_add, Nat.cast_one]
    rw [lintegral_add_left (measurable_of_countable _), lintegral_const,
      measure_univ, one_mul, IH]
    calc
      _ = (RealCoin.pmf p true + RealCoin.pmf p false) *
          (n * ENNReal.ofReal (p : ℝ)) + RealCoin.pmf p true := by ring
      _ = _ := by rw [RealCoin.pmf_sum]; simp [RealCoin.pmf]; ring

@[simp] theorem law_zero (n : ℕ) : law 0 n = Measure.dirac 0 := by
  induction n with
  | zero => rfl
  | succ n IH => simp [law, RealCoin.pmf, IH]

@[simp] theorem law_one (n : ℕ) : law 1 n = Measure.dirac n := by
  induction n with
  | zero => rfl
  | succ n IH => simp [law, RealCoin.pmf, IH]

end

end SampLib.Binomial
