import SampLib.Latent.LatentSpec
import SampLib.Continuous.Rejection

/-! # Conditioning a deferred draw on an accepted event

An accepted state retains its original posterior and oracle ownership. The initial
law is the proposal law conditioned on acceptance; all later observations simply
refine an already accepted state.
-/

open Set MeasureTheory

namespace SampLib.LatentReal.Conditioning

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω]

/-- A proposal state whose observations have established acceptance. -/
structure Accepted (D : Model Ω S) (initial : S) (A : Set Ω) where
  state : S
  refines_initial : D.refines initial state
  accepted : ∀ᵐ x ∂D.posterior state, x ∈ A

variable (D : Model Ω S) (initial : S) (A : Set Ω)
  (hmass : D.posterior initial A ≠ 0)

/-- The initial conditional state has not yet selected an accepted proposal. -/
def posterior : Option (Accepted D initial A) → Measure Ω
  | none => Rejection.law (D.posterior initial) A hmass
  | some q => D.posterior q.state

instance (q : Option (Accepted D initial A)) :
    IsProbabilityMeasure (posterior D initial A hmass q) := by
  cases q <;> dsimp [posterior] <;> infer_instance

/-- Accepted states may only refine an accepted state, never return to initialization. -/
def Refines : Option (Accepted D initial A) → Option (Accepted D initial A) → Prop
  | none, _ => True
  | some _, none => False
  | some p, some q => D.refines p.state q.state

private theorem accepted_absolutelyContinuous (q : Accepted D initial A) :
    D.posterior q.state ≪ Rejection.law (D.posterior initial) A hmass := by
  have h := (D.absolutelyContinuous q.refines_initial).restrict A
  rw [Measure.restrict_eq_self_of_ae_mem q.accepted] at h
  exact h.smul_right (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))

private theorem initial_absolutelyContinuous :
    Rejection.law (D.posterior initial) A hmass ≪ D.posterior initial :=
  (Measure.absolutelyContinuous_restrict (μ := D.posterior initial) (s := A)).smul_left _

/-- The same latent real and shrinking error, viewed under the conditional law. -/
def model : Model Ω (Option (Accepted D initial A)) where
  posterior := posterior D initial A hmass
  probability _ := inferInstance
  value := D.value
  measurable_value := D.measurable_value
  refines := Refines D initial A
  refines_refl s := by
    cases s with
    | none => trivial
    | some p => exact D.refines_refl p.state
  refines_trans := by
    intro p q r hpq hqr
    cases p <;> cases q <;> cases r <;> simp_all [Refines]
    exact D.refines_trans hpq hqr
  absolutelyContinuous := by
    intro p q hpq
    cases p with
    | none =>
      cases q with
      | none => exact Measure.AbsolutelyContinuous.rfl
      | some q => exact accepted_absolutelyContinuous D initial A hmass q
    | some p =>
      cases q with
      | none => exact False.elim hpq
      | some q => exact D.absolutelyContinuous hpq
  error := D.error
  error_tendsto s := by
    cases s with
    | none =>
      exact (initial_absolutelyContinuous D initial A hmass).ae_le (D.error_tendsto initial)
    | some q => exact D.error_tendsto q.state

end

end SampLib.LatentReal.Conditioning
