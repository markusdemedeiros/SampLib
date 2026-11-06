import SampLib.Weighted.Laws.FiniteImage
import SampLib.Common.Laws.BinaryRounding

/-! # The law of integer-emulated floating multiplication

A uniform binary word is multiplied, rounded to a binary significand with ties to even,
and divided by the word modulus. The finite image law keeps every collision.
-/

open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal

namespace SampLib.FloatingMultiply

noncomputable section

/-- The exact integer output associated with one source word. -/
def output (n bits precision word : ℕ) : ℕ :=
  BinaryRounding.round (n * word) precision / 2 ^ bits

/-- The finite word-image law, retaining every collision introduced by rounding and division. -/
def law (n bits precision : ℕ) : Measure ℕ :=
  FiniteImage.law (2 ^ bits) (output n bits precision)

instance (n bits precision : ℕ) : IsProbabilityMeasure (law n bits precision) := by
  let : NeZero (2 ^ bits) := ⟨by positivity⟩
  unfold law
  infer_instance

/-- Exact biased PMF: count words mapping to an output, then divide by the word count. -/
theorem law_singleton (n bits precision x : ℕ) :
    law n bits precision {x} =
      ((Finset.range (2 ^ bits)).filter (fun word =>
        BinaryRounding.round (n * word) precision / 2 ^ bits = x)).card /
          ((2 ^ bits : ℕ) : ℝ≥0∞) := FiniteImage.law_singleton _ _ _

/-- Continuation credit is the exact finite average, including infinite credits. -/
theorem expectation (n bits precision : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ x, F x ∂law n bits precision =
      (∑ word ∈ Finset.range (2 ^ bits), F (output n bits precision word)) / (2 ^ bits : ℕ) :=
  FiniteImage.lintegral_law _ _ _

end

end SampLib.FloatingMultiply
