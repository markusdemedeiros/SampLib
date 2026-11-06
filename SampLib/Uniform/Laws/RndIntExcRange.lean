module

public import SampLib.Uniform.Laws.UniformInt

@[expose] public section

/-! # Uniform law on a half-open integer interval -/

open scoped ENNReal

namespace SampLib.RndIntExcRange

noncomputable section

open MeasureTheory

/-- Shift the exclusive uniform offset law to `[lo, hi)`. -/
def law (lo hi : ℤ) (_h : lo < hi) : Measure ℤ :=
  (UniformInt.law (hi - lo).toNat).map (fun k : ℕ => lo + (k : ℤ))

instance (lo hi : ℤ) (h : lo < hi) : IsProbabilityMeasure (law lo hi h) := by
  let : NeZero (hi - lo).toNat := ⟨by omega⟩
  unfold law
  infer_instance

/-- Translation transports the offset expectation to the interval law. -/
theorem expectation (lo hi : ℤ) (h : lo < hi) (F : ℤ → ℝ≥0∞) :
    ∫⁻ k, F (lo + (k : ℤ)) ∂UniformInt.law (hi - lo).toNat = ∫⁻ z, F z ∂law lo hi h := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

end

end SampLib.RndIntExcRange
