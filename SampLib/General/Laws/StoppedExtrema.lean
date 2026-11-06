import SampLib.Combinatorial.SampleWithReplacement

/-! # Independent extrema at positive random counts -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.StoppedExtrema

noncomputable section

/-- Select the smaller or larger of two observations. -/
def combine (takeMin : Bool) (x y : ℤ) : ℤ := if takeMin then min x y else max x y

/-- Fold fresh independent observations into the current extremum. -/
def tailLaw (takeMin : Bool) (μ : Measure ℤ) (n : ℕ) (current : ℤ) : Measure ℤ :=
  (SampleWithReplacement.law μ n).map
    (fun xs => (List.ofFn xs).foldl (combine takeMin) current)

instance (takeMin : Bool) (μ : Measure ℤ) [IsProbabilityMeasure μ] (n : ℕ) (current : ℤ) :
    IsProbabilityMeasure (tailLaw takeMin μ n current) where
  measure_univ := by
    rw [tailLaw, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

@[simp] theorem tailLaw_zero (takeMin : Bool) (μ : Measure ℤ) (current : ℤ) :
    tailLaw takeMin μ 0 current = Measure.dirac current := by
  simp [tailLaw, SampleWithReplacement.law,
    Measure.map_dirac' (measurable_of_countable _)]

/-- A nonempty independent sample starts with one observation and `n` further draws. -/
def finiteLaw (takeMin : Bool) (μ : Measure ℤ) (n : ℕ) : Measure ℤ :=
  μ.bind (tailLaw takeMin μ n)

instance (takeMin : Bool) (μ : Measure ℤ) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (finiteLaw takeMin μ n) where
  measure_univ := by
    rw [finiteLaw, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
    simp

@[simp] theorem finiteLaw_zero (takeMin : Bool) (μ : Measure ℤ) :
    finiteLaw takeMin μ 0 = μ := by
  change μ.bind (fun x => tailLaw takeMin μ 0 x) = μ
  simp only [tailLaw_zero]
  exact Measure.bind_dirac

/-- Mix the nonempty extrema against the positive stopping count. -/
def law (takeMin : Bool) (ν : Measure ℕ) (μ : Measure ℤ) : Measure ℤ :=
  ν.bind (fun n => finiteLaw takeMin μ (n - 1))

instance (takeMin : Bool) (ν : Measure ℕ) [IsProbabilityMeasure ν]
    (μ : Measure ℤ) [IsProbabilityMeasure μ] : IsProbabilityMeasure (law takeMin ν μ) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
    simp

/-- One independent observation updates the extremum before the tail fold. -/
theorem tail_expectation (takeMin : Bool) (μ : Measure ℤ) [IsProbabilityMeasure μ]
    (n : ℕ) (current : ℤ) (F : ℤ → ℝ≥0∞) :
    ∫⁻ x, ∫⁻ z, F z ∂tailLaw takeMin μ n (combine takeMin current x) ∂μ =
      ∫⁻ z, F z ∂tailLaw takeMin μ (n + 1) current := by
  rw [tailLaw, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    SampleWithReplacement.lintegral_law_succ μ n _ (measurable_of_countable _)]
  simp only [tailLaw, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    List.ofFn_succ, List.foldl_cons, Fin.cons_zero, Fin.cons_succ]

/-- Condition first on the stopping count, then on the initial observation. -/
theorem expectation (takeMin : Bool) (ν : Measure ℕ) [IsProbabilityMeasure ν]
    (μ : Measure ℤ) [IsProbabilityMeasure μ] (F : ℤ → ℝ≥0∞) :
    ∫⁻ n, ∫⁻ x, ∫⁻ z, F z ∂tailLaw takeMin μ (n - 1) x ∂μ ∂ν =
      ∫⁻ z, F z ∂law takeMin ν μ := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]
  simp only [finiteLaw, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]

theorem combine_min (current x : ℤ) :
    combine true current x = if x < current then x else current := by
  by_cases h : x < current
  · simp [combine, h, min_eq_right h.le]
  · simp [combine, h, min_eq_left (not_lt.mp h)]

theorem combine_max (current x : ℤ) :
    combine false current x = if current < x then x else current := by
  by_cases h : current < x
  · simp [combine, h, max_eq_right h.le]
  · simp [combine, h, max_eq_left (not_lt.mp h)]

end

end SampLib.StoppedExtrema
