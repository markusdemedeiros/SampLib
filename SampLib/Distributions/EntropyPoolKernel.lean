import SampLib.Distributions.EntropyPoolAbsorption

/-! # Exact state kernels for quotient/remainder recycling

A known pool can return a deterministic output. Its law retains the output and
both new pool coordinates. Fresh-bit acceptance resets the pool; only an immediate
accepted rectangle can retain a larger quotient.
-/

open Finset MeasureTheory
open scoped ENNReal

namespace SampLib.EntropyPool

noncomputable section

abbrev JointResult := ℕ × ℕ × ℕ

def cutoff (n width : ℕ) : ℕ := width / n * n

theorem cutoff_add_mod (n width : ℕ) : cutoff n width + width % n = width := by
  simpa only [cutoff, Nat.mul_comm] using Nat.div_add_mod width n

theorem rejected_valid (n width value : ℕ) (hv : value < width)
    (ha : ¬value < cutoff n width) : value - cutoff n width < width % n := by
  have h := cutoff_add_mod n width
  omega

theorem accepted_valid (n width value : ℕ) (hn : 0 < n)
    (ha : value < cutoff n width) : value % n < n ∧ value / n < width / n := by
  exact ⟨Nat.mod_lt _ hn, (Nat.div_lt_iff_lt_mul hn).mpr ha⟩

/-- A fixed initial rank determines whether a quotient survives or the pool resets. -/
def residualState (n value width : ℕ) : ℕ × ℕ :=
  if value < cutoff n width then (value / n, width / n) else (0, 1)

theorem residualState_valid (n value width : ℕ) (hn : 0 < n) :
    (residualState n value width).1 < (residualState n value width).2 := by
  unfold residualState
  split_ifs with ha
  · exact (accepted_valid n width value hn ha).2
  · decide

/-- Finite source credit retains each fixed pool's exact joint state update. -/
def jointCredit (n value width T : ℕ) (F : JointResult → ℝ≥0∞) : ℝ≥0∞ :=
  if value < cutoff n width then F (value % n, value / n, width / n)
  else BitRecycler.credit .lower n (fun r => F (r, 0, 1)) T
    (width % n) (value - cutoff n width)

/-- The joint leaf law of one fixed pool, including its retained quotient. -/
def recycledKernel (n value width : ℕ) : Measure JointResult :=
  if value < cutoff n width then Measure.dirac (value % n, value / n, width / n)
  else (boundedKernel n (width % n) (value - cutoff n width)).map (fun r => (r, 0, 1))

/-- Validity is needed for normalization, not to define the finite-leaf measure. -/
def recycledLaw (n value width : ℕ) (_hn : 0 < n) (_hv : value < width) :
    Measure JointResult := recycledKernel n value width

instance (n value width : ℕ) (hn : 0 < n) (hv : value < width) :
    IsProbabilityMeasure (recycledLaw n value width hn hv) where
  measure_univ := by
    change recycledKernel n value width Set.univ = 1
    unfold recycledKernel
    split_ifs with ha
    · simp
    · have hprob : IsProbabilityMeasure
          (boundedKernel n (width % n) (value - cutoff n width)) :=
        inferInstanceAs (IsProbabilityMeasure (boundedLaw n (width % n)
          (value - cutoff n width) hn (Nat.mod_lt _ hn) (rejected_valid n width value hv ha)))
      rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
      simpa only [Set.preimage_univ] using hprob.measure_univ

/-- Exact joint continuation credit, without replacing a fixed rank by a uniform rank. -/
theorem recycledKernel_expectation (n value width : ℕ) (F : JointResult → ℝ≥0∞) :
    (∫⁻ z, F z ∂recycledKernel n value width) =
      if value < cutoff n width then F (value % n, value / n, width / n)
      else ∫⁻ r, F (r, 0, 1) ∂boundedKernel n (width % n) (value - cutoff n width) := by
  by_cases ha : value < cutoff n width
  · simp [recycledKernel, ha]
  · simp only [recycledKernel, ite_eq_right ha]
    rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

/-- The eventual joint expectation and a geometric cutoff fund every finite source horizon. -/
theorem joint_horizon_bound (n value width T : ℕ) (hn : 0 < n) (hv : value < width)
    (F : JointResult → ℝ≥0∞) :
    jointCredit n value width T F ≤ (∫⁻ z, F z ∂recycledLaw n value width hn hv) +
      ((n - 1 : ℕ) : ℝ≥0∞) / 2 ^ T := by
  change _ ≤ (∫⁻ z, F z ∂recycledKernel n value width) + _
  rw [recycledKernel_expectation]
  unfold jointCredit
  split_ifs with ha
  · exact le_add_right le_rfl
  · exact horizon_lintegral_bound n T (width % n) (value - cutoff n width)
      (fun r => F (r, 0, 1)) hn (Nat.mod_lt _ hn) (rejected_valid n width value hv ha)

/-- A uniform initial rank splits into a quotient rectangle and a reset-state tail. -/
theorem recycled_ensemble (n width : ℕ) (hn : 0 < n) (F : JointResult → ℝ≥0∞) :
    (∑ v ∈ range width, ∫⁻ z, F z ∂recycledKernel n v width) =
      (∑ k ∈ range (width / n), ∑ r ∈ range n, F (r, k, width / n)) +
        (((width % n : ℕ) : ℝ≥0∞) / n) * ∑ r ∈ range n, F (r, 0, 1) := by
  simp_rw [recycledKernel_expectation]
  have hsplit := SampLib.EntropyPool.split width n hn
    (fun r k => F (r, k, width / n))
    (fun v => ∫⁻ r, F (r, 0, 1) ∂boundedKernel n (width % n) v)
  have hraw : (∑ v ∈ range width,
      if v < cutoff n width then F (v % n, v / n, width / n)
      else ∫⁻ r, F (r, 0, 1) ∂boundedKernel n (width % n) (v - cutoff n width)) =
      (∑ k ∈ range (width / n), ∑ r ∈ range n, F (r, k, width / n)) +
        ∑ v ∈ range (width % n), ∫⁻ r, F (r, 0, 1) ∂boundedKernel n (width % n) v := by
    simpa only [cutoff, Nat.mul_comm] using hsplit
  rw [hraw, ensemble_expectation n (width % n) hn (Nat.mod_lt _ hn)]

/-- Residual state under an initially uniform rank: uniform quotient, or a reset pool. -/
def residualLaw (n width : ℕ) (_hw : 0 < width) : Measure (ℕ × ℕ) :=
  (((n : ℝ≥0∞) / width) • ∑ k ∈ range (width / n), Measure.dirac (k, width / n)) +
    ((((width % n : ℕ) : ℝ≥0∞) / width) • Measure.dirac (0, 1))

instance (n width : ℕ) (hw : 0 < width) : IsProbabilityMeasure (residualLaw n width hw) where
  measure_univ := by
    have hsplit : (n : ℝ≥0∞) * (width / n : ℕ) + (width % n : ℕ) = width := by
      exact_mod_cast Nat.div_add_mod width n
    simp only [residualLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    simp only [Measure.finsetSum_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
      sum_const, card_range, nsmul_eq_mul, mul_one]
    calc
      _ = ((n : ℝ≥0∞) * (width / n : ℕ) + (width % n : ℕ)) / width := by
        simp only [ENNReal.div_eq_inv_mul]
        ring
      _ = 1 := by
        rw [hsplit]
        exact ENNReal.div_self (by exact_mod_cast hw.ne') (by finiteness)

theorem residualLaw_expectation (n width : ℕ) (hw : 0 < width) (G : ℕ × ℕ → ℝ≥0∞) :
    (∫⁻ z, G z ∂residualLaw n width hw) =
      ((n : ℝ≥0∞) / width) * ∑ k ∈ range (width / n), G (k, width / n) +
        (((width % n : ℕ) : ℝ≥0∞) / width) * G (0, 1) := by
  simp [residualLaw, lintegral_add_measure, lintegral_finsetSum_measure]

/-- Average the exact kernels over a genuinely uniform initial rank. -/
def uniformPoolLaw (n width : ℕ) (_hn : 0 < n) (_hw : 0 < width) : Measure JointResult :=
  ((width : ℝ≥0∞)⁻¹ • (∑ v ∈ range width, recycledKernel n v width))

instance (n width : ℕ) (hn : 0 < n) (hw : 0 < width) :
    IsProbabilityMeasure (uniformPoolLaw n width hn hw) where
  measure_univ := by
    have hsum : (∑ v ∈ range width, recycledKernel n v width Set.univ) = width := by
      calc
        _ = ∑ v ∈ range width, (1 : ℝ≥0∞) := by
          apply sum_congr rfl
          intro v hv
          have hp : IsProbabilityMeasure (recycledLaw n v width hn (mem_range.mp hv)) :=
            inferInstance
          exact hp.measure_univ
        _ = _ := by simp
    simp only [uniformPoolLaw, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
    rw [hsum]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast hw.ne') (by finiteness)

theorem uniformPoolLaw_expectation (n width : ℕ) (hn : 0 < n) (hw : 0 < width)
    (F : JointResult → ℝ≥0∞) :
    (∫⁻ z, F z ∂uniformPoolLaw n width hn hw) =
      ((∑ k ∈ range (width / n), ∑ r ∈ range n, F (r, k, width / n)) +
        (((width % n : ℕ) : ℝ≥0∞) / n) * ∑ r ∈ range n, F (r, 0, 1)) / width := by
  simp only [uniformPoolLaw, lintegral_smul_measure, lintegral_finsetSum_measure, smul_eq_mul]
  rw [recycled_ensemble n width hn]
  simp only [ENNReal.div_eq_inv_mul]

/-- Output and residual state are independent after averaging an initially uniform pool.
The residual quotient is conditionally uniform on its retained width. -/
theorem uniformPoolLaw_eq_prod (n width : ℕ) (hn : 0 < n) (hw : 0 < width) :
    uniformPoolLaw n width hn hw = (UniformInt.law n).prod (residualLaw n width hw) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [uniformPoolLaw_expectation, lintegral_prod _ hF.aemeasurable,
    UniformInt.lintegral_law]
  simp_rw [residualLaw_expectation]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  rw [sum_comm (s := range n) (t := range (width / n))]
  have hninv : (n : ℝ≥0∞)⁻¹ * n = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by finiteness)
  simp only [ENNReal.div_eq_inv_mul]
  symm
  calc
    _ = (n : ℝ≥0∞)⁻¹ * n * (width : ℝ≥0∞)⁻¹ *
        (∑ k ∈ range (width / n), ∑ r ∈ range n, F (r, k, width / n)) +
        (width : ℝ≥0∞)⁻¹ * (width % n : ℕ) * (n : ℝ≥0∞)⁻¹ *
          ∑ r ∈ range n, F (r, 0, 1) := by ring
    _ = _ := by rw [hninv]; ring

end

end SampLib.EntropyPool
