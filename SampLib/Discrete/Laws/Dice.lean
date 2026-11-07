import SampLib.Uniform.Laws.UniformInt

/-! # Sums of fair dice

The law is the convolution of independent uniforms on `1, …, sides`.
-/

open scoped ENNReal

namespace SampLib.Dice

noncomputable section

open MeasureTheory Measure

/-- Sum of `n` independent `sides`-sided dice. -/
def law (sides : ℕ) : ℕ → Measure ℕ
  | 0 => dirac 0
  | n + 1 => ((law sides n).prod (UniformInt.law sides)).map
      (fun z => 1 + z.2 + z.1)

instance (sides n : ℕ) [NeZero sides] : IsProbabilityMeasure (law sides n) := by
  induction n with
  | zero => dsimp [law]; infer_instance
  | succ n ih =>
    let := ih
    constructor
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Credit remaining for the new die after observing the other dice. -/
def continuation (sides : ℕ) (F : ℕ → ℝ≥0∞) (rest : ℕ) : ℝ≥0∞ :=
  ∫⁻ k, F (1 + k + rest) ∂UniformInt.law sides

/-- Independence identifies the nested expectation with the sum's convolution. -/
theorem expectation (sides n : ℕ) [NeZero sides] (F : ℕ → ℝ≥0∞) :
    ∫⁻ rest, continuation sides F rest ∂law sides n =
      ∫⁻ total, F total ∂law sides (n + 1) := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]
  rfl

end

end SampLib.Dice
