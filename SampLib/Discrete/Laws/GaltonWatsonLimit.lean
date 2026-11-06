module

public import SampLib.Common.Laws.PoissonGenerating
public import SampLib.Common.Laws.PoissonThinning
public import Mathlib.MeasureTheory.Measure.GiryMonad

@[expose] public section

/-! # Galton–Watson progeny as an increasing limit

Height truncation gives an increasing sequence of finite-tree subprobabilities.
Their limit satisfies the branching equation of the Poisson offspring law.
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

end

end SampLib.GaltonWatson
