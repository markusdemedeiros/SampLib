module

public import SampLib.Distributions.DyadicRefinement
public import SampLib.Distributions.LatentReal.Interval
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

/-! # Joint posterior credits for two cached uniforms

Each prefix fixes its own posterior cell. Continuation credits are functions of
both latent coordinates, so subsequent arithmetic retains their joint dependence.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.LatentUniformProduct

noncomputable section

/-- The two independent streams before any credit-weighted observations. -/
def law (left right : List Bool) : Measure (ℝ × ℝ) :=
  (DyadicPosterior.law left).prod (DyadicPosterior.law right)

instance (left right : List Bool) : IsProbabilityMeasure (law left right) := by
  unfold law
  infer_instance

/-- Simultaneous prefix extension retains all previously learned null-set facts. -/
theorem law_refines {left left' right right' : List Bool}
    (hl : left <+: left') (hr : right <+: right') :
    law left' right' ≪ law left right :=
  (DyadicPosterior.law_refines hl).prod (DyadicPosterior.law_refines hr)

/-- Credit left after integrating the unobserved right coordinate. -/
def leftCredit (right : List Bool) (F : ℝ × ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, F (x, y) ∂DyadicPosterior.law right

/-- Credit right after integrating the unobserved left coordinate. -/
def rightCredit (left : List Bool) (F : ℝ × ℝ → ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, F (x, y) ∂DyadicPosterior.law left

theorem measurable_leftCredit (right : List Bool) {F : ℝ × ℝ → ℝ≥0∞}
    (hF : Measurable F) : Measurable (leftCredit right F) :=
  hF.lintegral_prod_right'

theorem measurable_rightCredit (left : List Bool) {F : ℝ × ℝ → ℝ≥0∞}
    (hF : Measurable F) : Measurable (rightCredit left F) :=
  hF.lintegral_prod_left'

/-- Observing the left stream first uses the exact joint continuation expectation. -/
theorem expectation_left (left right : List Bool) (F : ℝ × ℝ → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ z, F z ∂law left right =
      ∫⁻ x, leftCredit right F x ∂DyadicPosterior.law left :=
  lintegral_prod F hF.aemeasurable

/-- The alternative evaluation order preserves the same joint credit. -/
theorem expectation_right (left right : List Bool) (F : ℝ × ℝ → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ z, F z ∂law left right =
      ∫⁻ y, rightCredit left F y ∂DyadicPosterior.law right :=
  lintegral_prod_symm F hF.aemeasurable

/-- Coordinate-wise almost-sure facts lift without changing the joint credit kernel. -/
theorem ae_coordinates (left right : List Bool) {P Q : ℝ → Prop}
    (hl : ∀ᵐ x ∂DyadicPosterior.law left, P x)
    (hr : ∀ᵐ y ∂DyadicPosterior.law right, Q y) :
    ∀ᵐ z ∂law left right, P z.1 ∧ Q z.2 := by
  exact ((Measure.quasiMeasurePreserving_fst
    (μ := DyadicPosterior.law left) (ν := DyadicPosterior.law right)).ae hl).and
      ((Measure.quasiMeasurePreserving_snd
        (μ := DyadicPosterior.law left) (ν := DyadicPosterior.law right)).ae hr)

/-- Interval reads enclose the same two coordinates of the shared latent pair. -/
theorem ae_enclosures (left right : List Bool) (a b : LatentReal.RationalInterval)
    (hl : ∀ᵐ x ∂DyadicPosterior.law left, a.Contains x)
    (hr : ∀ᵐ y ∂DyadicPosterior.law right, b.Contains y) :
    ∀ᵐ z ∂law left right, a.Contains z.1 ∧ b.Contains z.2 :=
  ae_coordinates left right hl hr

end

end SampLib.LatentUniformProduct
