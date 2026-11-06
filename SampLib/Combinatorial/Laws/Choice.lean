module

public import SampLib.Uniform.Laws.UniformInt

@[expose] public section

/-! # Uniform law on finite positions -/

open scoped ENNReal

namespace SampLib.Choice

noncomputable section

open MeasureTheory

/-- Extend an in-range natural position to a total finite-index map. -/
def position (n : ℕ) [NeZero n] (k : ℕ) : Fin n :=
  ⟨k % n, Nat.mod_lt _ (NeZero.pos n)⟩

theorem position_of_lt {n : ℕ} [NeZero n] (k : ℕ) (hk : k < n) :
    position n k = ⟨k, hk⟩ := Fin.ext (Nat.mod_eq_of_lt hk)

/-- Uniform finite-position law. -/
def law (n : ℕ) [NeZero n] : Measure (Fin n) :=
  (UniformInt.law n).map (position n)

instance (n : ℕ) [NeZero n] : IsProbabilityMeasure (law n) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- The lookup's continuation credit is averaged over positions. -/
theorem lintegral_law (n : ℕ) [NeZero n] (F : Fin n → ℝ≥0∞) :
    ∫⁻ i, F i ∂law n = (∑ k ∈ Finset.range n, F (position n k)) / n := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    UniformInt.lintegral_law]

end

end SampLib.Choice
