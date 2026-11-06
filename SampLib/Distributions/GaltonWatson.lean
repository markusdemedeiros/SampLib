module

public import SampLib.Distributions.PoissonGenerating
public import SampLib.Distributions.PoissonThinning
public import Mathlib.MeasureTheory.Measure.GiryMonad

@[expose] public section

/-! # Total progeny of a subcritical Poisson Galton–Watson tree

Height truncation gives an increasing sequence of finite-tree subprobabilities.
Their limit is normalized because the Poisson offspring generating function has
no fixed point below one in the subcritical regime.
-/

open MeasureTheory Measure
open scoped ENNReal NNReal

namespace SampLib.GaltonWatson

noncomputable section

/-- Independent total progenies of a forest with a specified number of roots. -/
def forest (μ : Measure ℕ) : ℕ → Measure ℕ
  | 0 => dirac 0
  | n + 1 => μ.bind (fun x => (forest μ n).map (x + ·))

theorem forest_expectation (μ : Measure ℕ) (n : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ s, F s ∂forest μ (n + 1) = ∫⁻ x, ∫⁻ y, F (x + y) ∂forest μ n ∂μ := by
  rw [forest, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]
  congr 1
  funext x
  exact lintegral_map (measurable_of_countable _) (measurable_of_countable _)

/-- Attach an independent Poisson family to a new root. -/
def grow (r : ℝ≥0) (μ : Measure ℕ) : Measure ℕ :=
  (ProbabilityTheory.poissonMeasure r).bind (fun n => (forest μ n).map (1 + ·))

theorem grow_expectation (r : ℝ≥0) (μ : Measure ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ s, F s ∂grow r μ =
      ∫⁻ n, ∫⁻ s, F (1 + s) ∂forest μ n ∂ProbabilityTheory.poissonMeasure r := by
  rw [grow, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]
  congr 1
  funext n
  exact lintegral_map (measurable_of_countable _) (measurable_of_countable _)

private theorem measure_le_of_integrals {μ ν : Measure ℕ}
    (h : ∀ F : ℕ → ℝ≥0∞, ∫⁻ x, F x ∂μ ≤ ∫⁻ x, F x ∂ν) : μ ≤ ν := by
  apply Measure.le_iff.mpr
  intro s hs
  simpa [lintegral_indicator hs] using h (s.indicator (fun _ => 1))

theorem forest_mono {μ ν : Measure ℕ} (h : μ ≤ ν) (n : ℕ) :
    forest μ n ≤ forest ν n := by
  induction n with
  | zero => rfl
  | succ n IH =>
    apply measure_le_of_integrals
    intro F
    rw [forest_expectation, forest_expectation]
    exact lintegral_mono' h (fun x => lintegral_mono' IH le_rfl)

theorem grow_mono (r : ℝ≥0) {μ ν : Measure ℕ} (h : μ ≤ ν) : grow r μ ≤ grow r ν := by
  apply measure_le_of_integrals
  intro F
  rw [grow_expectation, grow_expectation]
  exact lintegral_mono (fun n => lintegral_mono' (forest_mono h n) le_rfl)

/-- At height zero no finite tree has yet been admitted. -/
def truncation (r : ℝ≥0) : ℕ → Measure ℕ
  | 0 => 0
  | d + 1 => grow r (truncation r d)

theorem truncation_mono (r : ℝ≥0) : Monotone (truncation r) := by
  apply monotone_nat_of_le_succ
  intro d
  induction d with
  | zero => exact bot_le
  | succ d IH => exact grow_mono r IH

/-- Increasing limits on this countable state space are computed atom by atom. -/
def increasingLimit (μ : ℕ → Measure ℕ) : Measure ℕ :=
  Measure.sum (fun k => (⨆ d, μ d {k}) • dirac k)

theorem lintegral_increasingLimit (μ : ℕ → Measure ℕ) (hμ : Monotone μ)
    (F : ℕ → ℝ≥0∞) :
    ∫⁻ x, F x ∂increasingLimit μ = ⨆ d, ∫⁻ x, F x ∂μ d := by
  simp only [increasingLimit, lintegral_sum_measure, lintegral_smul_measure,
    lintegral_dirac, smul_eq_mul, ENNReal.iSup_mul]
  have h := lintegral_iSup (μ := Measure.count)
    (f := fun d k => μ d {k} * F k) (fun _ => measurable_of_countable _)
    (fun i j hij k => mul_le_mul_left (Measure.le_iff'.mp (hμ hij) {k}) (F k))
  simpa [lintegral_countable', mul_comm] using h

private theorem diagonal_sup (f : ℕ → ℕ → ℝ≥0∞)
    (h₁ : ∀ j, Monotone (fun i => f i j)) (h₂ : ∀ i, Monotone (f i)) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k := by
  apply le_antisymm
  · refine iSup_le fun i => iSup_le fun j => ?_
    exact le_iSup_of_le (max i j) ((h₁ j (le_max_left _ _)).trans
      (h₂ (max i j) (le_max_right _ _)))
  · exact iSup_le fun k => le_iSup_of_le k (le_iSup _ k)

/-- Finite independent forests commute with the increasing height limit. -/
theorem forest_increasingLimit (μ : ℕ → Measure ℕ) (hμ : Monotone μ)
    (n : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ s, F s ∂forest (increasingLimit μ) n =
      ⨆ d, ∫⁻ s, F s ∂forest (μ d) n := by
  induction n generalizing F with
  | zero => simp [forest]
  | succ n IH =>
    simp only [forest_expectation]
    rw [lintegral_increasingLimit μ hμ]
    simp_rw [IH]
    have hm : Monotone (fun j x => ∫⁻ y, F (x + y) ∂forest (μ j) n) :=
      fun i j hij x => lintegral_mono' (forest_mono (hμ hij) n) le_rfl
    simp_rw [lintegral_iSup (fun _ => measurable_of_countable _) hm]
    exact diagonal_sup _
      (fun j i k hik => lintegral_mono' (hμ hik) le_rfl)
      (fun i j k hjk => lintegral_mono
        (fun x => lintegral_mono' (forest_mono (hμ hjk) n) le_rfl))

/-- The offspring operation commutes with increasing height limits. -/
theorem grow_increasingLimit (r : ℝ≥0) (μ : ℕ → Measure ℕ) (hμ : Monotone μ)
    (F : ℕ → ℝ≥0∞) :
    ∫⁻ s, F s ∂grow r (increasingLimit μ) =
      ⨆ d, ∫⁻ s, F s ∂grow r (μ d) := by
  simp only [grow_expectation, forest_increasingLimit μ hμ]
  rw [lintegral_iSup (fun _ => measurable_of_countable _)
    (fun i j hij n => lintegral_mono' (forest_mono (hμ hij) n) le_rfl)]

/-- Total progeny of a finite Poisson Galton–Watson tree. -/
def law (r : ℝ≥0) : Measure ℕ := increasingLimit (truncation r)

theorem branching (r : ℝ≥0) : grow r (law r) = law r := by
  apply Measure.ext
  intro s hs
  have h := grow_increasingLimit r (truncation r) (truncation_mono r)
    (s.indicator (fun _ => 1))
  have hm : Monotone (fun d => ∫⁻ x, s.indicator (fun _ => 1) x ∂truncation r d) :=
    fun i j hij => lintegral_mono' (truncation_mono r hij) le_rfl
  have hshift : (⨆ d, ∫⁻ x, s.indicator (fun _ => 1) x ∂grow r (truncation r d)) =
      ⨆ d, ∫⁻ x, s.indicator (fun _ => 1) x ∂truncation r d := by
    simpa only [truncation] using hm.iSup_nat_add 1
  have he := h.trans (hshift.trans
    (lintegral_increasingLimit _ (truncation_mono r) _).symm)
  simpa [law, lintegral_indicator hs] using he

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
