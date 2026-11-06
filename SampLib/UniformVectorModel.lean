import SampLib.Distributions.LatentReal.UniformVector
import SampLib.LatentVectorSpec
import SampLib.LatentUniform

/-! # A common latent world for independent deferred uniforms -/

open ProbLang
open scoped ENNReal

namespace SampLib.UniformVector

noncomputable section

/-- The common world carries all coordinates and their cached prefixes. -/
def world (n : ℕ) : LatentReal.Model (Fin n → ℝ) (Fin n → List Bool) where
  posterior := law
  probability _ := inferInstance
  value _ := 0
  measurable_value := measurable_const
  refines := Refines
  refines_refl p i := List.prefix_refl (p i)
  refines_trans hpq hqr i := (hpq i).trans (hqr i)
  absolutelyContinuous := law_refines
  error _ _ := 0
  error_tendsto _ := Filter.Eventually.of_forall fun _ => tendsto_const_nhds

/-- A coordinate projects the same joint world; observing it retains every other coordinate. -/
def view {n : ℕ} (i : Fin n) : LatentReal.Model (Fin n → ℝ) (Fin n → List Bool) :=
  { world n with
    value := fun x => x i
    measurable_value := measurable_pi_apply i
    error bits _ := (2 ^ bits : ℝ)⁻¹
    error_tendsto _ := Filter.Eventually.of_forall fun _ =>
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)) }

theorem view_sameWorld {n : ℕ} (i : Fin n) : LatentReal.Model.SameWorld (world n) (view i) :=
  ⟨fun _ => rfl, fun _ _ => Iff.rfl⟩

/-- The actual jointly observable vector has the full product-posterior law. -/
@[simp] theorem vectorLaw_eq_law {n : ℕ} (p : Fin n → List Bool) :
    LatentReal.vectorLaw (world n) (fun i => view i) p = law p := by
  change (law p).map (fun x => x) = law p
  exact MeasureTheory.Measure.map_id

/-- Every coordinate starts with an owned unsampled cell. -/
def initial (n : ℕ) : Fin n → List Bool := fun _ => []

@[simp] theorem initial_law (n : ℕ) :
    law (initial n) = MeasureTheory.Measure.pi (fun _ : Fin n => DyadicPosterior.unitLaw) := by
  simp only [law, initial, DyadicPosterior.law_nil]

/-- A coordinate's finite interval is valid under the updated joint posterior. -/
theorem view_interval_encloses {n : ℕ} (p : Fin n → List Bool) (i : Fin n)
    (q : List Bool) (bits : ℕ) (hread : UniformBag.readRefines (p i) bits q) :
    (view i).Encloses (Function.update p i q) bits (LatentUniform.interval q bits) := by
  have hI := LatentUniform.interval_encloses hread
  unfold LatentReal.Model.Encloses at hI ⊢
  change ∀ᵐ z ∂law (Function.update p i q),
    (LatentUniform.interval q bits).Contains (z i) ∧
      (LatentUniform.interval q bits).upperReal - (LatentUniform.interval q bits).lowerReal ≤
        (2 ^ bits : ℝ)⁻¹
  apply ae_coordinate (Function.update p i q) i (P := fun x =>
    (LatentUniform.interval q bits).Contains x ∧
      (LatentUniform.interval q bits).upperReal - (LatentUniform.interval q bits).lowerReal ≤
        (2 ^ bits : ℝ)⁻¹)
  simpa only [Function.update_self, LatentUniform.model, id_eq] using hI

end

end SampLib.UniformVector
