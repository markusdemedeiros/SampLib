import SampLib.Latent.Laws.UniformVectorModel
import SampLib.Latent.LatentVectorSpec
import SampLib.Latent.LatentUniform

/-! # Joint views and enclosures of the common uniform world -/

open ProbLang
open scoped ENNReal

namespace SampLib.UniformVector

noncomputable section

theorem view_sameWorld {n : ℕ} (i : Fin n) : LatentReal.Model.SameWorld (world n) (view i) :=
  ⟨fun _ => rfl, fun _ _ => Iff.rfl⟩

/-- The actual jointly observable vector has the full product-posterior law. -/
@[simp] theorem vectorLaw_eq_law {n : ℕ} (p : Fin n → List Bool) :
    LatentReal.vectorLaw (world n) (fun i => view i) p = law p := by
  change (law p).map (fun x => x) = law p
  exact MeasureTheory.Measure.map_id

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
