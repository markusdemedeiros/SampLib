module

public import SampLib.Uniform.Laws.RealCoin

@[expose] public section

/-! # Binomial trial sums

The law is the `n`-fold convolution of a Bernoulli count: a successful trial
shifts the previous sum by one, and a failed trial leaves it unchanged.
-/

open scoped ENNReal

namespace SampLib.Binomial

noncomputable section

open MeasureTheory Measure

/-- The sum of `n` independent Bernoulli(`p`) indicators. -/
def law (p : unitInterval) : ℕ → Measure ℕ
  | 0 => dirac 0
  | n + 1 => (RealCoin.pmf p true • (law p n).map Nat.succ) +
      (RealCoin.pmf p false • law p n)

instance (p : unitInterval) (n : ℕ) : IsProbabilityMeasure (law p n) := by
  induction n with
  | zero => dsimp [law]; infer_instance
  | succ n IH =>
    let := IH
    constructor
    simpa [law, Measure.map_apply (measurable_of_countable Nat.succ)] using RealCoin.pmf_sum p

/-- Conditional expectation after the first indicator. -/
def continuation (p : unitInterval) (n : ℕ) (F : ℕ → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  ∫⁻ k, F (if b then k + 1 else k) ∂law p n

@[simp] theorem expectation_zero (p : unitInterval) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, F k ∂law p 0 = F 0 := by simp [law]

/-- Splitting off one indicator preserves the binomial expectation. -/
theorem expectation (p : unitInterval) (n : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ b, continuation p n F b ∂RealCoin.law p = ∫⁻ k, F k ∂law p (n + 1) := by
  rw [RealCoin.lintegral_law]
  simp [law, RealCoin.credit, continuation,
    lintegral_map (measurable_of_countable F) (measurable_of_countable Nat.succ),
    smul_eq_mul, Nat.succ_eq_add_one]

end

end SampLib.Binomial
