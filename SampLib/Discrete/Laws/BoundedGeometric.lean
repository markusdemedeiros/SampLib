import SampLib.Uniform.Laws.RealCoin

/-! # Capped geometric failures

The law counts failures before success, capped at `n`. Its recurrence separates
immediate success from a failed trial followed by a shifted capped count.
-/

open scoped ENNReal

namespace SampLib.BoundedGeometric

noncomputable section

open MeasureTheory Measure

/-- The geometric failure count capped at `n`, including the mass at the cap. -/
def law (p : unitInterval) : ℕ → Measure ℕ
  | 0 => dirac 0
  | n + 1 => (RealCoin.pmf p true • dirac 0) +
      (RealCoin.pmf p false • (law p n).map Nat.succ)

instance (p : unitInterval) (n : ℕ) : IsProbabilityMeasure (law p n) := by
  induction n with
  | zero => dsimp [law]; infer_instance
  | succ n IH =>
    let := IH
    constructor
    simpa [law, Measure.map_apply (measurable_of_countable Nat.succ)] using RealCoin.pmf_sum p

/-- Conditional continuation credit after the first flip. -/
def continuation (p : unitInterval) (n : ℕ) (F : ℕ → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F 0 else ∫⁻ k, F (k + 1) ∂law p n

@[simp] theorem expectation_zero (p : unitInterval) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, F k ∂law p 0 = F 0 := by simp [law]

/-- One success/failure split preserves the capped geometric expectation. -/
theorem expectation (p : unitInterval) (n : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ b, continuation p n F b ∂RealCoin.law p = ∫⁻ k, F k ∂law p (n + 1) := by
  rw [RealCoin.lintegral_law]
  simp [law, RealCoin.credit, continuation,
    lintegral_map (measurable_of_countable F) (measurable_of_countable Nat.succ),
    smul_eq_mul, Nat.succ_eq_add_one]

end

end SampLib.BoundedGeometric
