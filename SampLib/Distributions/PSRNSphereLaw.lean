module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.MeasureTheory.Measure.Map

@[expose] public section

/-! # The joint direction law of independent Gaussian coordinates

Normalization acts on the whole vector. Its rotation invariance is inherited
from the standard Gaussian, without treating the normalized coordinates as independent.
-/

open MeasureTheory ProbabilityTheory NormedSpace
open scoped ENNReal RealInnerProductSpace

namespace SampLib.PSRNSphereLaw

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem measurable_normalize : Measurable (NormedSpace.normalize : E → E) := by
  unfold NormedSpace.normalize
  fun_prop

/-- Standard Gaussian direction, interpreted as a measure on the ambient vector space. -/
def law (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure E :=
  (stdGaussian E).map NormedSpace.normalize

instance : IsProbabilityMeasure (law E) := by
  unfold law
  constructor
  rw [Measure.map_apply measurable_normalize MeasurableSet.univ]
  simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The normalizing vector and its rotated image have the same length. -/
theorem normalize_map (rotation : E ≃ₗᵢ[ℝ] E) (x : E) :
    NormedSpace.normalize (rotation x) = rotation (NormedSpace.normalize x) := by
  simp [NormedSpace.normalize, map_smul]

/-- Orthogonal transformations preserve the complete direction law. -/
theorem rotation_invariant (rotation : E ≃ₗᵢ[ℝ] E) :
    (law E).map rotation = law E := by
  have hr : Measurable rotation := rotation.continuous.measurable
  rw [law, Measure.map_map hr measurable_normalize]
  calc
    (stdGaussian E).map (rotation ∘ NormedSpace.normalize) =
        (stdGaussian E).map (NormedSpace.normalize ∘ rotation) := by
      congr 1
      funext x
      exact (normalize_map rotation x).symm
    _ = ((stdGaussian E).map rotation).map NormedSpace.normalize :=
      (Measure.map_map measurable_normalize hr).symm
    _ = law E := by rw [stdGaussian_map rotation]; rfl

private theorem stdGaussian_ne_dirac [Nontrivial E] (center : E) :
    stdGaussian E ≠ Measure.dirac center := by
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have hv : Var[innerSL ℝ x; stdGaussian E] = ‖x‖ ^ 2 := by
    rw [variance_dual_stdGaussian, innerSL_apply_norm]
  intro hdirac
  rw [hdirac, variance_dirac] at hv
  have hnorm := norm_pos_iff.mpr hx
  nlinarith

private instance [Nontrivial E] : NullSingletonClass (stdGaussian E) :=
  IsGaussian.nullSingletonClass stdGaussian_ne_dirac

/-- A nontrivial Gaussian vector has unit direction almost surely. -/
theorem ae_norm_eq_one [Nontrivial E] : ∀ᵐ x ∂law E, ‖x‖ = 1 := by
  rw [law, ae_map_iff measurable_normalize.aemeasurable
    (measurableSet_eq_fun measurable_norm measurable_const)]
  exact ((stdGaussian E).ae_ne 0).mono fun x hx => NormedSpace.norm_normalize hx

/-- Expected output credit is assigned jointly before normalization. -/
theorem expectation_preservation (F : E → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ direction, F direction ∂law E = ∫⁻ x, F (NormedSpace.normalize x) ∂stdGaussian E :=
  lintegral_map hF measurable_normalize

end

end SampLib.PSRNSphereLaw
