module

public import Metrology.ProbLang.Reals
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

/-! # Irwin–Hall law as an iterated unit-uniform convolution -/

open Set ProbLang
open LawfulProbLangℝ (unifUnit)
open scoped ENNReal

namespace SampLib.UniformSum

noncomputable section

section mathematics

open MeasureTheory Measure

/-- The `n`-fold convolution of the unit-uniform law, starting at zero. -/
def law : ℕ → Measure ℝ
  | 0 => dirac 0
  | n + 1 => (unifUnit.prod (law n)).map (fun z : ℝ × ℝ => z.1 + z.2)

instance (n : ℕ) : IsProbabilityMeasure (law n) := by
  induction n with
  | zero => unfold law; infer_instance
  | succ n ih =>
    have := ih
    unfold law
    infer_instance

/-- Conditional credit after the new uniform draw. -/
def credit (n : ℕ) (F : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, F (x + y) ∂law n

theorem measurable_credit (n : ℕ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    Measurable (credit n F) :=
  (hF.comp (measurable_fst.add measurable_snd)).lintegral_prod_right'

/-- Convolution expectation is the successive expectation of the two summands. -/
theorem expectation_preservation (n : ℕ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, credit n F x ∂unifUnit = ∫⁻ z, F z ∂law (n + 1) := by
  have hsum : Measurable (fun z : ℝ × ℝ => z.1 + z.2) :=
    measurable_fst.add measurable_snd
  rw [law, lintegral_map hF hsum]
  exact (lintegral_prod _ (hF.comp hsum).aemeasurable).symm

end mathematics

end

end SampLib.UniformSum
