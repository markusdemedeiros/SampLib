module

public import SampLib.Latent.Laws.Model
public import SampLib.Latent.Laws.UniformVector

@[expose] public section

/-! # A common latent world for independent deferred uniforms

The world carries every coordinate and its cached prefix. Each coordinate view projects
the same joint posterior.
-/

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

/-- Every coordinate starts with an owned unsampled cell. -/
def initial (n : ℕ) : Fin n → List Bool := fun _ => []

@[simp] theorem initial_law (n : ℕ) :
    law (initial n) = MeasureTheory.Measure.pi (fun _ : Fin n => DyadicPosterior.unitLaw) := by
  simp only [law, initial, DyadicPosterior.law_nil]

end

end SampLib.UniformVector
