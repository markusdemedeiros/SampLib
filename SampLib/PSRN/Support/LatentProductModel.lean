import SampLib.Latent.LatentViews

/-! # Independent latent worlds with shared product views

A product constructor allocates both component states. Once allocated, every
coordinate view retains that one combined ownership and arbitrary joint credit.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.LatentReal.ProductModel

noncomputable section

variable {Ω₁ Ω₂ S₁ S₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

/-- The full product posterior, after each component's current refinement. -/
def posterior (L : Model Ω₁ S₁) (R : Model Ω₂ S₂) (s : S₁ × S₂) : Measure (Ω₁ × Ω₂) :=
  (L.posterior s.1).prod (R.posterior s.2)

instance (L : Model Ω₁ S₁) (R : Model Ω₂ S₂) (s : S₁ × S₂) :
    IsProbabilityMeasure (posterior L R s) := by unfold posterior; infer_instance

/-- The first projection, retaining both physical refinement states. -/
def left (L : Model Ω₁ S₁) (R : Model Ω₂ S₂) : Model (Ω₁ × Ω₂) (S₁ × S₂) where
  posterior := posterior L R
  probability := fun _ => inferInstance
  value := fun z => L.value z.1
  measurable_value := L.measurable_value.comp measurable_fst
  refines s t := L.refines s.1 t.1 ∧ R.refines s.2 t.2
  refines_refl s := ⟨L.refines_refl s.1, R.refines_refl s.2⟩
  refines_trans hst htu := ⟨L.refines_trans hst.1 htu.1, R.refines_trans hst.2 htu.2⟩
  absolutelyContinuous h := (L.absolutelyContinuous h.1).prod (R.absolutelyContinuous h.2)
  error n z := L.error n z.1
  error_tendsto s :=
    (Measure.quasiMeasurePreserving_fst
      (μ := L.posterior s.1) (ν := R.posterior s.2)).ae (L.error_tendsto s.1)

/-- The second projection of exactly the same owned product world. -/
def right (L : Model Ω₁ S₁) (R : Model Ω₂ S₂) : Model (Ω₁ × Ω₂) (S₁ × S₂) :=
  { left L R with
    value := fun z => R.value z.2
    measurable_value := R.measurable_value.comp measurable_snd
    error := fun n z => R.error n z.2
    error_tendsto := fun s =>
      (Measure.quasiMeasurePreserving_snd
        (μ := L.posterior s.1) (ν := R.posterior s.2)).ae (R.error_tendsto s.2) }

/-- Sequentially observing the two projections never changes the underlying world. -/
theorem sameWorld (L : Model Ω₁ S₁) (R : Model Ω₂ S₂) :
    (left L R).SameWorld (right L R) := ⟨fun _ => rfl, fun _ _ => Iff.rfl⟩

/-- Conditional credit for constructing or observing the left component. -/
def leftCredit (R : Model Ω₂ S₂) (s : S₂) (F : Ω₁ × Ω₂ → ℝ≥0∞) (x : Ω₁) : ℝ≥0∞ :=
  ∫⁻ y, F (x, y) ∂R.posterior s

/-- Conditional credit for constructing or observing the right component. -/
def rightCredit (L : Model Ω₁ S₁) (s : S₁) (F : Ω₁ × Ω₂ → ℝ≥0∞) (y : Ω₂) : ℝ≥0∞ :=
  ∫⁻ x, F (x, y) ∂L.posterior s

theorem measurable_leftCredit (R : Model Ω₂ S₂) (s : S₂) {F : Ω₁ × Ω₂ → ℝ≥0∞}
    (hF : Measurable F) : Measurable (leftCredit R s F) := hF.lintegral_prod_right'

theorem measurable_rightCredit (L : Model Ω₁ S₁) (s : S₁) {F : Ω₁ × Ω₂ → ℝ≥0∞}
    (hF : Measurable F) : Measurable (rightCredit L s F) := hF.lintegral_prod_left'

/-- Tonelli allocates a full joint continuation through the first component. -/
theorem expectation_left (L : Model Ω₁ S₁) (R : Model Ω₂ S₂) (s : S₁ × S₂)
    (F : Ω₁ × Ω₂ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F z ∂posterior L R s = ∫⁻ x, leftCredit R s.2 F x ∂L.posterior s.1 :=
  lintegral_prod F hF.aemeasurable

/-- Swapping the order of conditioning preserves the same joint expectation. -/
theorem expectation_right (L : Model Ω₁ S₁) (R : Model Ω₂ S₂) (s : S₁ × S₂)
    (F : Ω₁ × Ω₂ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F z ∂posterior L R s = ∫⁻ y, rightCredit L s.1 F y ∂R.posterior s.2 :=
  lintegral_prod_symm F hF.aemeasurable

/-- The observable pair law is the product of the component observable laws. -/
theorem law_eq_product (L : Model Ω₁ S₁) (R : Model Ω₂ S₂) (s : S₁ × S₂) :
    (posterior L R s).map (Prod.map L.value R.value) = (L.law s.1).prod (R.law s.2) :=
  (Measure.map_prod_map (L.posterior s.1) (R.posterior s.2)
    L.measurable_value R.measurable_value).symm

/-- A left interval encloses the same first coordinate of the full posterior. -/
theorem encloses_left (L : Model Ω₁ S₁) (R : Model Ω₂ S₂)
    {s : S₁} (t : S₂) {n : ℕ} {I : RationalInterval} (hI : L.Encloses s n I) :
    (left L R).Encloses (s, t) n I :=
  (Measure.quasiMeasurePreserving_fst
    (μ := L.posterior s) (ν := R.posterior t)).ae hI

/-- A right interval encloses the same second coordinate of the full posterior. -/
theorem encloses_right (L : Model Ω₁ S₁) (R : Model Ω₂ S₂)
    (s : S₁) {t : S₂} {n : ℕ} {I : RationalInterval} (hI : R.Encloses t n I) :
    (right L R).Encloses (s, t) n I :=
  (Measure.quasiMeasurePreserving_snd
    (μ := L.posterior s) (ν := R.posterior t)).ae hI

end

end SampLib.LatentReal.ProductModel
