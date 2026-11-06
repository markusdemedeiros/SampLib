import SampLib.Distributions.FiniteProductPosterior
import SampLib.LatentRepresentedVectorSpec
import SampLib.LatentMeasuredError

/-! # One shared latent world for a finite family of independent components -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.LatentReal.PiModel

noncomputable section

variable {n : ℕ} {Ω S : Fin n → Type} [∀ i, MeasurableSpace (Ω i)]

/-- The full product posterior of all current component states. -/
def posterior (Ds : ∀ i, Model (Ω i) (S i)) (s : ∀ i, S i) : Measure (∀ i, Ω i) :=
  Measure.pi (fun i => (Ds i).posterior (s i))

instance (Ds : ∀ i, Model (Ω i) (S i)) (s : ∀ i, S i) :
    IsProbabilityMeasure (posterior Ds s) := by unfold posterior; infer_instance

/-- Coordinates refine independently while retaining their joint posterior. -/
def world (Ds : ∀ i, Model (Ω i) (S i)) : Model (∀ i, Ω i) (∀ i, S i) where
  posterior := posterior Ds
  probability _ := inferInstance
  value _ := 0
  measurable_value := measurable_const
  refines s t := ∀ i, (Ds i).refines (s i) (t i)
  refines_refl s i := (Ds i).refines_refl (s i)
  refines_trans hst htu i := (Ds i).refines_trans (hst i) (htu i)
  absolutelyContinuous h :=
    FiniteProductPosterior.absolutelyContinuous Ω _ _ (fun i => (Ds i).absolutelyContinuous (h i))
  error _ _ := 0
  error_tendsto _ := Filter.Eventually.of_forall fun _ => tendsto_const_nhds

/-- A coordinate's value and uncertainty are projections of the one common world. -/
def view (Ds : ∀ i, Model (Ω i) (S i)) (i : Fin n) : Model (∀ i, Ω i) (∀ i, S i) :=
  { world Ds with
    value x := (Ds i).value (x i)
    measurable_value := (Ds i).measurable_value.comp (measurable_pi_apply i)
    error bits x := (Ds i).error bits (x i)
    error_tendsto s :=
      (measurePreserving_eval (fun j => (Ds j).posterior (s j)) i).quasiMeasurePreserving.ae
        ((Ds i).error_tendsto (s i)) }

theorem sameWorld (Ds : ∀ i, Model (Ω i) (S i)) (i : Fin n) :
    (world Ds).SameWorld (view Ds i) := ⟨fun _ => rfl, fun _ _ => Iff.rfl⟩

/-- A represented coordinate returns precisely its own interval in the product world. -/
def representation (Ds : ∀ i, Model (Ω i) (S i)) (Rs : ∀ i, Representation (Ds i)) (i : Fin n) :
    Representation (view Ds i) where
  interval bits x := (Rs i).interval bits (x i)
  measurable_lower bits := (Rs i).measurable_lower bits |>.comp (measurable_pi_apply i)
  measurable_upper bits := (Rs i).measurable_upper bits |>.comp (measurable_pi_apply i)
  measurable_denominator bits := (Rs i).measurable_denominator bits |>.comp (measurable_pi_apply i)
  approximates s :=
    (measurePreserving_eval (fun j => (Ds j).posterior (s j)) i).quasiMeasurePreserving.ae
      ((Rs i).approximates (s i))

/-- Independence belongs to the allocation world, before later shared arithmetic. -/
theorem vectorLaw_eq_pi (Ds : ∀ i, Model (Ω i) (S i)) (s : ∀ i, S i) :
    vectorLaw (world Ds) (view Ds) s = Measure.pi (fun i => (Ds i).law (s i)) := by
  change (Measure.pi (fun i => (Ds i).posterior (s i))).map
    (fun x i => (Ds i).value (x i)) = _
  exact Measure.pi_map_pi (fun i => (Ds i).measurable_value.aemeasurable)

theorem measurableError (Ds : ∀ i, Model (Ω i) (S i)) (i : Fin n)
    (herror : (Ds i).MeasurableError) : (view Ds i).MeasurableError :=
  fun bits => (herror bits).comp (measurable_pi_apply i)

end

end SampLib.LatentReal.PiModel
