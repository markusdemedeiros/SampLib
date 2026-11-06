module

public import SampLib.Distributions.LatentReal.DigitPosterior
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

@[expose] public section

/-! # The conditional next-digit kernel

The callback sees the current prefix, while its output credit contains the
posterior of the entire latent world. Zero-probability children remain in the
expectation identity and are excluded only when a callback actually returns.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SampLib.DigitPosterior

noncomputable section

variable {Ω : Type} [MeasurableSpace Ω]

/-- The next bit's conditional law given all cached digits. -/
def nextLaw (μ : Measure Ω) (digits : Ω → ℕ → Bool) (p : List Bool) : Measure Bool :=
  (law μ digits p).map (fun x => digits x p.length)

theorem nextLaw_probability (μ : Measure Ω) [IsFiniteMeasure μ]
    {digits : Ω → ℕ → Bool} (hd : ∀ n, Measurable (fun x => digits x n))
    (p : List Bool) (hp : μ (cylinder digits p) ≠ 0) :
    IsProbabilityMeasure (nextLaw μ digits p) := by
  have := probability μ digits p hp
  exact (Measure.isProbabilityMeasure_map_iff (hd p.length).aemeasurable).2 inferInstance

theorem nextLaw_singleton (μ : Measure Ω)
    {digits : Ω → ℕ → Bool} (hd : ∀ n, Measurable (fun x => digits x n))
    (p : List Bool) (b : Bool) :
    nextLaw μ digits p {b} = law μ digits p {x | digits x p.length = b} :=
  Measure.map_apply (hd p.length) (.singleton b)

/-- Conditional next-bit sampling preserves arbitrary joint continuation credit. -/
theorem next_expectation (μ : Measure Ω) [IsFiniteMeasure μ]
    {digits : Ω → ℕ → Bool} (hd : ∀ n, Measurable (fun x => digits x n))
    (p : List Bool) (F : Ω → ℝ≥0∞) :
    (∫⁻ b, (∫⁻ x, F x ∂law μ digits (p ++ [b])) ∂nextLaw μ digits p) =
      ∫⁻ x, F x ∂law μ digits p := by
  calc
    _ = ∑ b : Bool, (∫⁻ x, F x ∂law μ digits (p ++ [b])) *
        nextLaw μ digits p {b} := lintegral_fintype _
    _ = ∑ b : Bool, (law μ digits p) {x | digits x p.length = b} *
        ∫⁻ x, F x ∂law μ digits (p ++ [b]) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [nextLaw_singleton μ hd]
      exact mul_comm _ _
    _ = _ := expectation_preservation μ hd p F

/-- A sampled bit with positive probability gives another reachable cache state. -/
theorem next_supported (μ : Measure Ω)
    {digits : Ω → ℕ → Bool} (hd : ∀ n, Measurable (fun x => digits x n))
    (p : List Bool) (b : Bool) (hb : nextLaw μ digits p {b} ≠ 0) :
    μ (cylinder digits (p ++ [b])) ≠ 0 := by
  rw [nextLaw_singleton μ hd, law,
    cond_apply (measurableSet_cylinder hd p), ← cylinder_extend] at hb
  exact (mul_ne_zero_iff.mp hb).2

end

end SampLib.DigitPosterior
