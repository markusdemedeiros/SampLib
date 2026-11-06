module

public import SampLib.Discrete.Laws.GaltonWatsonLimit

@[expose] public section

/-! # Total progeny of a subcritical Poisson Galton–Watson tree

The limit of the height truncations is normalized because the Poisson offspring
generating function has no fixed point below one in the subcritical regime. A
pending-root credit then follows the source's breadth-first recurrence.
-/

open MeasureTheory Measure
open scoped ENNReal NNReal

namespace SampLib.GaltonWatson

noncomputable section

/-- The forest mass is the probability that all its independent trees are finite. -/
theorem forest_mass (μ : Measure ℕ) (n : ℕ) :
    forest μ n Set.univ = (μ Set.univ) ^ n := by
  induction n with
  | zero => simp [forest]
  | succ n IH =>
    rw [forest, Measure.bind_apply MeasurableSet.univ
      (measurable_of_countable _).aemeasurable]
    simp [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ,
      IH, pow_succ, mul_comm]

theorem grow_mass (r : ℝ≥0) (μ : Measure ℕ) :
    grow r μ Set.univ =
      ∫⁻ n, (μ Set.univ) ^ n ∂ProbabilityTheory.poissonMeasure r := by
  rw [grow, Measure.bind_apply MeasurableSet.univ
    (measurable_of_countable _).aemeasurable]
  congr 1
  funext n
  simp [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ, forest_mass]

theorem grow_mass_le_one (r : ℝ≥0) (μ : Measure ℕ) (hμ : μ Set.univ ≤ 1) :
    grow r μ Set.univ ≤ 1 := by
  rw [grow_mass]
  calc
    _ ≤ ∫⁻ _ : ℕ, 1 ∂ProbabilityTheory.poissonMeasure r :=
      lintegral_mono (fun n => pow_le_one₀ zero_le hμ)
    _ = 1 := by simp

theorem truncation_mass (r : ℝ≥0) (d : ℕ) : truncation r d Set.univ ≤ 1 := by
  induction d with
  | zero => simp [truncation]
  | succ d IH => exact grow_mass_le_one r _ IH

theorem law_mass_le_one (r : ℝ≥0) : law r Set.univ ≤ 1 := by
  have h := lintegral_increasingLimit (truncation r) (truncation_mono r) (fun _ => 1)
  simp only [lintegral_one] at h
  rw [law, h]
  exact iSup_le (truncation_mass r)

/-- Subcriticality excludes every extinction fixed point below one. -/
theorem law_mass (r : ℝ≥0) (hr : r < 1) : law r Set.univ = 1 := by
  let q := law r Set.univ
  have hq : q ≤ 1 := law_mass_le_one r
  have hqfin : q ≠ ∞ := ne_top_of_le_ne_top (by simp) hq
  have hfixed : q = ENNReal.ofReal (Real.exp ((r : ℝ) * (q.toReal - 1))) := by
    calc
      q = grow r (law r) Set.univ := congrArg (fun μ : Measure ℕ => μ Set.univ)
        (branching r).symm
      _ = _ := by
        rw [grow_mass]
        calc
          _ = ∫⁻ n, ENNReal.ofReal (q.toReal ^ n)
              ∂ProbabilityTheory.poissonMeasure r := by
            apply lintegral_congr
            intro n
            rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg,
              ENNReal.ofReal_toReal hqfin]
          _ = _ := Distributions.lintegral_poisson_pow r q.toReal ENNReal.toReal_nonneg

  have hqr : q.toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (by simp) hq
  have hfixr : q.toReal = Real.exp ((r : ℝ) * (q.toReal - 1)) := by
    simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le] using
      congrArg ENNReal.toReal hfixed
  have hr' : (r : ℝ) < 1 := by exact_mod_cast hr
  have hqr' : q.toReal = 1 := by
    have he := Real.add_one_le_exp ((r : ℝ) * (q.toReal - 1))
    nlinarith
  apply (ENNReal.toReal_eq_toReal_iff' hqfin (by simp)).mp
  simpa using hqr'

instance (r : ℝ≥0) [hr : Fact (r < 1)] : IsProbabilityMeasure (law r) where
  measure_univ := law_mass r hr.out

/-- Concatenating independent forests adds their root counts. -/
theorem forest_add (μ : Measure ℕ) (m n : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ s, F s ∂forest μ (m + n) =
      ∫⁻ x, ∫⁻ y, F (x + y) ∂forest μ n ∂forest μ m := by
  induction m generalizing F with
  | zero => simp [forest]
  | succ m IH =>
    rw [Nat.succ_add, forest_expectation]
    simp_rw [IH]
    rw [forest_expectation]
    simp only [Nat.add_assoc]

/-- Expected output credit of a forest added to the population already explored. -/
def credit (r : ℝ≥0) (pending population : ℕ) (F : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ s, F (population + s) ∂forest (law r) pending

@[simp] theorem credit_zero (r : ℝ≥0) (population : ℕ) (F : ℕ → ℝ≥0∞) :
    credit r 0 population F = F population := by simp [credit, forest]

/-- Exploring the first root reveals its offspring and leaves the remaining forest. -/
theorem credit_recurrence (r : ℝ≥0) (pending population : ℕ) (F : ℕ → ℝ≥0∞) :
    credit r (pending + 1) population F =
      ∫⁻ k, credit r (pending + k) (population + 1) F
        ∂ProbabilityTheory.poissonMeasure r := by
  rw [credit, forest_expectation]
  have h := grow_expectation r (law r)
    (fun x => ∫⁻ y, F (population + (x + y)) ∂forest (law r) pending)
  rw [branching] at h
  rw [h]
  apply lintegral_congr
  intro k
  rw [credit, Nat.add_comm pending k, forest_add]
  simp only [Nat.add_assoc]

@[simp] theorem initial_credit (r : ℝ≥0) (F : ℕ → ℝ≥0∞) :
    credit r 1 0 F = ∫⁻ n, F n ∂law r := by
  simp [credit, forest]

/-- The factorial recursion is the Poisson size-bias identity. -/
private theorem poisson_size_bias (r : ℝ≥0) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ≥0∞) * ProbabilityTheory.poissonMeasure r {n + 1} =
      (r : ℝ≥0∞) * ProbabilityTheory.poissonMeasure r {n} := by
  rw [ProbabilityTheory.poissonMeasure_singleton,
    ProbabilityTheory.poissonMeasure_singleton, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul r.coe_nonneg]
  congr 1
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

/-- The first offspring moment, in the same nonnegative arithmetic as credits. -/
theorem poisson_mean (r : ℝ≥0) :
    ∫⁻ n, (n : ℝ≥0∞) ∂ProbabilityTheory.poissonMeasure r = r := by
  rw [lintegral_countable', tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  simp_rw [poisson_size_bias]
  rw [ENNReal.tsum_mul_left]
  have h : (∑' n, ProbabilityTheory.poissonMeasure r {n}) = 1 := by
    simpa only [lintegral_countable', one_mul] using
      (show (∫⁻ _ : ℕ, 1 ∂ProbabilityTheory.poissonMeasure r) = 1 by simp)
  rw [h, mul_one]

@[simp] theorem law_zero_atom (r : ℝ≥0) : law r {0} = 0 := by
  calc
    _ = grow r (law r) {0} := congrArg (fun μ : Measure ℕ => μ {0}) (branching r).symm
    _ = 0 := by
      have he : (fun n : ℕ => 1 + n) ⁻¹' ({0} : Set ℕ) = ∅ := by ext n; simp
      simp [grow, Measure.bind_apply (measurableSet_singleton _)
        (measurable_of_countable _).aemeasurable,
        Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _), he]

@[simp] theorem law_zero_rate : law 0 = dirac 1 := by
  calc
    _ = grow 0 (law 0) := (branching 0).symm
    _ = _ := by
      simp [grow, Distributions.poissonMeasure_zero, forest,
        Measure.dirac_bind (measurable_of_countable _),
        Measure.map_dirac' (measurable_of_countable _)]

end

end SampLib.GaltonWatson
