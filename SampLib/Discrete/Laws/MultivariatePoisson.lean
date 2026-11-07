import Metrology.ProbLang.Discrete
import SampLib.Discrete.Laws.PoissonRational

/-! # Shared-component multivariate Poisson law

Each coordinate adds one common Poisson count to its own independent Poisson
count. The common count creates the dependence between coordinates.
-/

open scoped ENNReal NNReal

namespace SampLib.MultivariatePoisson

noncomputable section

open MeasureTheory Measure

/-- A nonnegative rational rate with its denominator certificate. -/
abbrev Rate := {p : ℕ × ℕ // 0 < p.2}

/-- Independent component counts, each shifted by the common count. -/
def components (shared : ℕ) : List Rate → Measure (List ℕ)
  | [] => dirac []
  | r :: rs => ((ProbabilityTheory.poissonMeasure
      (PoissonRational.rate r.val.1 r.val.2)).prod (components shared rs)).map
      (fun p => (shared + p.1) :: p.2)

instance (shared : ℕ) (rs : List Rate) : IsProbabilityMeasure (components shared rs) := by
  induction rs with
  | nil => dsimp [components]; infer_instance
  | cons r rs IH =>
    let := IH
    constructor
    rw [components, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- A single common Poisson component creates the dependence between coordinates. -/
def law (sharedRate : ℝ≥0) (rs : List Rate) : Measure (List ℕ) :=
  (ProbabilityTheory.poissonMeasure sharedRate).bind (fun shared => components shared rs)

instance (sharedRate : ℝ≥0) (rs : List Rate) : IsProbabilityMeasure (law sharedRate rs) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ
      (measurable_of_countable _).aemeasurable]
    simp

/-- Condition first on the common count, then on the independent coordinates. -/
theorem expectation (sharedRate : ℝ≥0) (rs : List Rate) (F : List ℕ → ℝ≥0∞) :
    (∫⁻ shared, ∫⁻ ns, F ns ∂components shared rs
      ∂ProbabilityTheory.poissonMeasure sharedRate) = ∫⁻ ns, F ns ∂law sharedRate rs := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]

theorem component_expectation (shared : ℕ) (r : Rate) (rs : List Rate)
    (F : List ℕ → ℝ≥0∞) :
    (∫⁻ n, ∫⁻ ns, F ((shared + n) :: ns) ∂components shared rs
      ∂ProbabilityTheory.poissonMeasure (PoissonRational.rate r.val.1 r.val.2)) =
      ∫⁻ ns, F ns ∂components shared (r :: rs) := by
  rw [components, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]

end

end SampLib.MultivariatePoisson
