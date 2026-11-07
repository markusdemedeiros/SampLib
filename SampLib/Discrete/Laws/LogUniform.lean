import SampLib.Discrete.Laws.LogUniformBuckets
import SampLib.Uniform.Laws.RndInt
import SampLib.Uniform.Laws.RndIntRange

/-! # Log-uniform law

A uniform magnitude level selects a bucket, then a uniform draw lands inside it.
The last bucket is clipped to the inclusive bound and keeps one level's mass.
-/

open scoped ENNReal

namespace SampLib.LogUniform

noncomputable section

open MeasureTheory Measure

/-- Zero is its own bucket; every positive level is an inclusive integer interval. -/
def bucket (maximum base level : ℕ) : Measure ℤ :=
  if level = 0 then dirac 0 else
    RndIntRange.law (lower maximum base level) (upper maximum base level)

instance (maximum base level : ℕ) : IsProbabilityMeasure (bucket maximum base level) := by
  unfold bucket
  split <;> infer_instance

/-- The finite mixture gives equal weight to every logarithmic level. -/
def law (maximum base : ℕ) : Measure ℤ :=
  (RndInt.law (lastLevel maximum base)).bind (bucket maximum base)

instance (maximum base : ℕ) : IsProbabilityMeasure (law maximum base) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
    simp

/-- Equal-weight bucket expectations are precisely the log-uniform expectation. -/
theorem expectation (maximum base : ℕ) (F : ℤ → ℝ≥0∞) :
    ∫⁻ level, (∫⁻ z, F z ∂bucket maximum base level)
      ∂RndInt.law (lastLevel maximum base) = ∫⁻ z, F z ∂law maximum base := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]

/-- Every logarithmic level carries the same mass, including a clipped last bucket. -/
theorem lintegral_law (maximum base : ℕ) (F : ℤ → ℝ≥0∞) :
    ∫⁻ z, F z ∂law maximum base =
      (∑ level ∈ Finset.range (lastLevel maximum base + 1),
        ∫⁻ z, F z ∂bucket maximum base level) / (lastLevel maximum base + 1) := by
  rw [← expectation, RndInt.expectation, Nat.cast_add, Nat.cast_one]

@[simp] theorem law_zero (base : ℕ) : law 0 base = dirac 0 := by
  apply Measure.ext_of_singleton
  intro z
  rw [← lintegral_indicator_one (measurableSet_singleton z), lintegral_law]
  simp [bucket]

/-- The inclusive level draw stays within the finite set of magnitude buckets. -/
theorem level_support (maximum base : ℕ) :
    ∀ᵐ level ∂RndInt.law (lastLevel maximum base), level ≤ lastLevel maximum base := by
  apply ae_iff_of_countable.mpr
  intro level hlevel
  by_contra h
  apply hlevel
  simp [RndInt.law, UniformInt.law, uniformOfFinset_apply_singleton,
    show ¬level < lastLevel maximum base + 1 by omega]

end

end SampLib.LogUniform
