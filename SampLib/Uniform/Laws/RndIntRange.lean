module

public import SampLib.Uniform.Laws.RndInt

@[expose] public section

/-! # Uniform law on an inclusive integer interval -/

open scoped ENNReal

namespace SampLib.RndIntRange

noncomputable section

open MeasureTheory

/-- Shift the inclusive uniform offset law to the requested integer interval. -/
def law (lo hi : ℤ) : Measure ℤ :=
  (RndInt.law (hi - lo).toNat).map (fun k : ℕ => lo + (k : ℤ))

instance (lo hi : ℤ) : IsProbabilityMeasure (law lo hi) := by
  unfold law
  infer_instance

/-- Translation transports the offset expectation to the interval law. -/
theorem expectation (lo hi : ℤ) (F : ℤ → ℝ≥0∞) :
    ∫⁻ k, F (lo + (k : ℤ)) ∂RndInt.law (hi - lo).toNat = ∫⁻ z, F z ∂law lo hi := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

end

end SampLib.RndIntRange
