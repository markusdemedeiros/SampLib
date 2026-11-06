import SampLib.Latent.LatentSpec

/-! # A common latent space for a mixture of deferred draws

The selector is part of the latent value. After selection, the posterior is the
chosen component, embedded into the same disjoint-sum space; it is never replaced
by an unrelated marginal. Initial-to-component refinement requires positive weight.
-/

open MeasureTheory
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.LatentReal.MixtureModel

noncomputable section

variable {Ω₁ Ω₂ S₁ S₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

private theorem inlEmbedding : MeasurableEmbedding (Sum.inl : Ω₁ → Ω₁ ⊕ Ω₂) :=
  ⟨Sum.inl_injective, measurable_inl, fun _ hs => hs.inl_image⟩

private theorem inrEmbedding : MeasurableEmbedding (Sum.inr : Ω₂ → Ω₁ ⊕ Ω₂) :=
  ⟨Sum.inr_injective, measurable_inr, fun _ hs => hs.inr_image⟩

/-- Almost-everywhere facts transport through a component injection without a
measurability assumption on the fact itself. -/
theorem ae_map_inl (μ : Measure Ω₁) (P : Ω₁ ⊕ Ω₂ → Prop) :
    (∀ᵐ z ∂μ.map Sum.inl, P z) ↔ ∀ᵐ x ∂μ, P (Sum.inl x) := by
  simp only [ae_iff, inlEmbedding.map_apply]
  rfl

theorem ae_map_inr (ν : Measure Ω₂) (P : Ω₁ ⊕ Ω₂ → Prop) :
    (∀ᵐ z ∂ν.map Sum.inr, P z) ↔ ∀ᵐ x ∂ν, P (Sum.inr x) := by
  simp only [ae_iff, inrEmbedding.map_apply]
  rfl

/-- A selector-weighted prior on the disjoint union of the component worlds. -/
def prior (p : unitInterval) (μ : Measure Ω₁) (ν : Measure Ω₂) : Measure (Ω₁ ⊕ Ω₂) :=
  (ofReal (p : ℝ) • μ.map Sum.inl) + (ofReal (1 - (p : ℝ)) • ν.map Sum.inr)

instance (p : unitInterval) (μ : Measure Ω₁) (ν : Measure Ω₂)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : IsProbabilityMeasure (prior p μ ν) := by
  refine ⟨?_⟩
  simp [prior, ← ENNReal.ofReal_add p.2.1 (sub_nonneg.mpr p.2.2)]

/-- Mixture credit is exactly the Bernoulli-weighted component credit, even at infinity. -/
theorem expectation_preservation (p : unitInterval) (μ : Measure Ω₁) (ν : Measure Ω₂)
    (F : Ω₁ ⊕ Ω₂ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F z ∂prior p μ ν =
      ofReal (p : ℝ) * (∫⁻ x, F (Sum.inl x) ∂μ) +
        ofReal (1 - (p : ℝ)) * (∫⁻ y, F (Sum.inr y) ∂ν) := by
  simp [prior, lintegral_map hF measurable_inl, lintegral_map hF measurable_inr,
    smul_eq_mul]

private theorem left_absolutelyContinuous (p : unitInterval) (hp : 0 < (p : ℝ))
    {μ μ' : Measure Ω₁} (ν : Measure Ω₂) (hμ : μ' ≪ μ) :
    μ'.map Sum.inl ≪ prior p μ ν := by
  have hc : ofReal (p : ℝ) ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  exact (inlEmbedding.absolutelyContinuous_map hμ).trans
    ((Measure.absolutelyContinuous_smul hc).add_right _)

private theorem right_absolutelyContinuous (p : unitInterval) (hp : (p : ℝ) < 1)
    (μ : Measure Ω₁) {ν ν' : Measure Ω₂} (hν : ν' ≪ ν) :
    ν'.map Sum.inr ≪ prior p μ ν := by
  have hc : ofReal (1 - (p : ℝ)) ≠ 0 := (ENNReal.ofReal_pos.mpr (sub_pos.mpr hp)).ne'
  exact (inrEmbedding.absolutelyContinuous_map hν).trans
    ((Measure.absolutelyContinuous_smul hc).add_right' _)

/-- A mixture is either not selected yet, or is in one component's refinement state. -/
inductive State (S₁ S₂ : Type)
  | initial
  | left (state : S₁)
  | right (state : S₂)

/-- Selected states carry normalized component posteriors in the same latent space. -/
def posterior (p : unitInterval) (L : Model Ω₁ S₁) (R : Model Ω₂ S₂)
    (i : S₁) (j : S₂) : State S₁ S₂ → Measure (Ω₁ ⊕ Ω₂)
  | .initial => prior p (L.posterior i) (R.posterior j)
  | .left s => (L.posterior s).map Sum.inl
  | .right t => (R.posterior t).map Sum.inr

/-- Selection is a refinement only for a component of positive prior mass. -/
def refines (p : unitInterval) (L : Model Ω₁ S₁) (R : Model Ω₂ S₂)
    (i : S₁) (j : S₂) : State S₁ S₂ → State S₁ S₂ → Prop
  | .initial, .initial => True
  | .initial, .left t => 0 < (p : ℝ) ∧ L.refines i t
  | .initial, .right t => (p : ℝ) < 1 ∧ R.refines j t
  | .left s, .left t => L.refines s t
  | .right s, .right t => R.refines s t
  | _, _ => False

private theorem refines_refl (p : unitInterval) (L : Model Ω₁ S₁) (R : Model Ω₂ S₂)
    (i : S₁) (j : S₂) (s : State S₁ S₂) : refines p L R i j s s := by
  cases s with
  | initial => trivial
  | left s => exact L.refines_refl s
  | right t => exact R.refines_refl t

private theorem refines_trans (p : unitInterval) (L : Model Ω₁ S₁) (R : Model Ω₂ S₂)
    (i : S₁) (j : S₂) {s t u : State S₁ S₂}
    (hst : refines p L R i j s t) (htu : refines p L R i j t u) :
    refines p L R i j s u := by
  cases s <;> cases t <;> cases u <;> simp_all only [refines, true_and]
  all_goals grind only [L.refines_trans, R.refines_trans]

private theorem posterior_absolutelyContinuous (p : unitInterval)
    (L : Model Ω₁ S₁) (R : Model Ω₂ S₂) (i : S₁) (j : S₂)
    {s t : State S₁ S₂} (h : refines p L R i j s t) :
    posterior p L R i j t ≪ posterior p L R i j s := by
  cases s with
  | initial =>
    cases t with
    | initial => exact Measure.AbsolutelyContinuous.rfl
    | left t => exact left_absolutelyContinuous p h.1 _ (L.absolutelyContinuous h.2)
    | right t => exact right_absolutelyContinuous p h.1 _ (R.absolutelyContinuous h.2)
  | left s =>
    cases t with
    | initial => exact False.elim h
    | left t => exact inlEmbedding.absolutelyContinuous_map (L.absolutelyContinuous h)
    | right t => exact False.elim h
  | right s =>
    cases t with
    | initial => exact False.elim h
    | left t => exact False.elim h
    | right t => exact inrEmbedding.absolutelyContinuous_map (R.absolutelyContinuous h)

/-- The two component models share one observable, selector-indexed latent model. -/
def model (p : unitInterval) (L : Model Ω₁ S₁) (R : Model Ω₂ S₂)
    (i : S₁) (j : S₂) : Model (Ω₁ ⊕ Ω₂) (State S₁ S₂) where
  posterior := posterior p L R i j
  probability := by
    intro s
    cases s <;> dsimp [posterior] <;> infer_instance
  value := Sum.elim L.value R.value
  measurable_value := L.measurable_value.sumElim R.measurable_value
  refines := refines p L R i j
  refines_refl := refines_refl p L R i j
  refines_trans := refines_trans p L R i j
  absolutelyContinuous := posterior_absolutelyContinuous p L R i j
  error := fun n => Sum.elim (L.error n) (R.error n)
  error_tendsto := by
    intro s
    have hl (s : S₁) : ∀ᵐ z ∂(L.posterior s).map Sum.inl,
        Filter.Tendsto (fun n => Sum.elim (L.error n) (R.error n) z)
          Filter.atTop (nhds 0) :=
      (ae_map_inl _ _).mpr (L.error_tendsto s)
    have hr (t : S₂) : ∀ᵐ z ∂(R.posterior t).map Sum.inr,
        Filter.Tendsto (fun n => Sum.elim (L.error n) (R.error n) z)
          Filter.atTop (nhds 0) :=
      (ae_map_inr _ _).mpr (R.error_tendsto t)
    cases s with
    | initial =>
      dsimp only [posterior, prior]
      apply ae_add_measure_iff.mpr
      exact ⟨Measure.smul_absolutelyContinuous.ae_le (hl i),
        Measure.smul_absolutelyContinuous.ae_le (hr j)⟩
    | left s => exact hl s
    | right t => exact hr t

/-- The initial observable law is the selector-weighted mixture of component laws. -/
theorem law_initial (p : unitInterval) (L : Model Ω₁ S₁) (R : Model Ω₂ S₂)
    (i : S₁) (j : S₂) :
    (model p L R i j).law .initial =
      (ofReal (p : ℝ) • L.law i) + (ofReal (1 - (p : ℝ)) • R.law j) := by
  have hm := L.measurable_value.sumElim R.measurable_value
  change (prior p (L.posterior i) (R.posterior j)).map (Sum.elim L.value R.value) = _
  rw [prior, Measure.map_add _ _ hm, Measure.map_smul _ hm.aemeasurable,
    Measure.map_smul _ hm.aemeasurable, Measure.map_map hm measurable_inl,
    Measure.map_map hm measurable_inr]
  rfl

/-- A selected left interval encloses the same sum-latent value. -/
theorem encloses_left (p : unitInterval) (L : Model Ω₁ S₁) (R : Model Ω₂ S₂)
    (i : S₁) (j : S₂) {s : S₁} {n : ℕ} {I : RationalInterval}
    (h : L.Encloses s n I) : (model p L R i j).Encloses (.left s) n I :=
  (ae_map_inl _ _).mpr h

/-- The right component uses the other injection into the same latent space. -/
theorem encloses_right (p : unitInterval) (L : Model Ω₁ S₁) (R : Model Ω₂ S₂)
    (i : S₁) (j : S₂) {s : S₂} {n : ℕ} {I : RationalInterval}
    (h : R.Encloses s n I) : (model p L R i j).Encloses (.right s) n I :=
  (ae_map_inr _ _).mpr h

end

end SampLib.LatentReal.MixtureModel
