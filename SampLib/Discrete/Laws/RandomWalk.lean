import SampLib.Bernoulli.Laws.VonNeumann

/-! # Symmetric random walk

The law is the `n`-fold convolution of the symmetric distribution on `{-1, 1}`.
-/

open scoped ENNReal

namespace SampLib.RandomWalk

noncomputable section

open MeasureTheory Measure

/-- Sum of `n` independent symmetric unit steps, starting at zero. -/
def law : ℕ → Measure ℤ
  | 0 => dirac 0
  | n + 1 => (RealCoin.pmf VonNeumann.fairBias true • (law n).map (fun z => z + 1)) +
      (RealCoin.pmf VonNeumann.fairBias false • (law n).map (fun z => z - 1))

instance (n : ℕ) : IsProbabilityMeasure (law n) := by
  induction n with
  | zero => dsimp [law]; infer_instance
  | succ n IH =>
    let := IH
    constructor
    simpa [law, Measure.map_apply (measurable_of_countable (fun z : ℤ => z + 1)),
      Measure.map_apply (measurable_of_countable (fun z : ℤ => z - 1))]
      using RealCoin.pmf_sum VonNeumann.fairBias

/-- Expected continuation credit after the first `n` steps. -/
def continuation (F : ℤ → ℝ≥0∞) (z : ℤ) : ℝ≥0∞ :=
  ∫⁻ b, F (if b then z + 1 else z - 1) ∂RealCoin.law VonNeumann.fairBias

@[simp] theorem expectation_zero (F : ℤ → ℝ≥0∞) :
    ∫⁻ z, F z ∂law 0 = F 0 := by simp [law]

/-- Adding an independent symmetric step preserves the convolution expectation. -/
theorem expectation (n : ℕ) (F : ℤ → ℝ≥0∞) :
    ∫⁻ z, continuation F z ∂law n = ∫⁻ z, F z ∂law (n + 1) := by
  simp only [continuation, RealCoin.lintegral_law, RealCoin.credit, law,
    lintegral_add_measure, lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_add_left (measurable_of_countable _),
    lintegral_const_mul _ (measurable_of_countable _),
    lintegral_const_mul _ (measurable_of_countable _),
    lintegral_map (measurable_of_countable F) (measurable_of_countable (fun z : ℤ => z + 1)),
    lintegral_map (measurable_of_countable F) (measurable_of_countable (fun z : ℤ => z - 1))]
  simp only [ite_true, Bool.false_eq_true, ite_false]

end

end SampLib.RandomWalk
