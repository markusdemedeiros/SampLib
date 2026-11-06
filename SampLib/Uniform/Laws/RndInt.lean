module

public import SampLib.Uniform.Laws.UniformInt

@[expose] public section

/-! # Uniform law with an inclusive upper bound -/

open Finset
open scoped ENNReal

namespace SampLib.RndInt

noncomputable section

open MeasureTheory

/-- Uniform law on `0, …, hi`. -/
abbrev law (hi : ℕ) := UniformInt.law (hi + 1)

/-- An inclusive bound contributes `hi+1` equally weighted outcomes. -/
theorem expectation (hi : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, F k ∂law hi = (∑ k ∈ range (hi + 1), F k) / ((hi + 1 : ℕ) : ℝ≥0∞) :=
  UniformInt.lintegral_law (hi + 1) F

/-- A zero bound always returns `0`. -/
theorem credit_zero (F : ℕ → ℝ≥0∞) : ∫⁻ k, F k ∂law 0 = F 0 := by
  simp [expectation]

end

end SampLib.RndInt
