module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

/-! # Erlang law as an iterated unit-exponential convolution -/

open scoped ENNReal

namespace SampLib.Erlang

noncomputable section

section mathematics

open MeasureTheory Measure

private instance : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
  ProbabilityTheory.isProbabilityMeasure_expMeasure zero_lt_one

/-- The law with positive shape `n + 1`: the sum of `n + 1` unit exponentials. -/
def law : ℕ → Measure ℝ
  | 0 => ProbabilityTheory.expMeasure 1
  | n + 1 => ((law n).prod (ProbabilityTheory.expMeasure 1)).map
      (fun z : ℝ × ℝ => z.2 + z.1)

@[simp] theorem law_zero : law 0 = ProbabilityTheory.expMeasure 1 := rfl

instance (n : ℕ) : IsProbabilityMeasure (law n) := by
  induction n with
  | zero => unfold law; infer_instance
  | succ n ih =>
    have := ih
    unfold law
    infer_instance

/-- Conditional credit after the recursively sampled partial sum. -/
def credit (F : ℝ → ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, F (x + y) ∂ProbabilityTheory.expMeasure 1

theorem measurable_credit (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    Measurable (credit F) :=
  (hF.comp (measurable_snd.add measurable_fst)).lintegral_prod_right'

/-- Exponential convolution gives the successive expectations in evaluation order. -/
theorem expectation_preservation (n : ℕ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ y, credit F y ∂law n = ∫⁻ z, F z ∂law (n + 1) := by
  have hadd : Measurable (fun z : ℝ × ℝ => z.2 + z.1) :=
    measurable_snd.add measurable_fst
  rw [law, lintegral_map hF hadd]
  exact (lintegral_prod _ (hF.comp hadd).aemeasurable).symm

end mathematics

end

end SampLib.Erlang
