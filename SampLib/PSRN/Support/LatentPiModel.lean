import SampLib.PSRN.Laws.FiniteProductPosterior
import SampLib.PSRN.Support.LatentRepresentedVectorSpec
import SampLib.Latent.LatentViews
import SampLib.Latent.Laws.MeasuredError
import SampLib.PSRN.Support.LatentRepresentedViews

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

open ProbLang

namespace SampLib.LatentReal.PiModel

noncomputable section

section ownership

open Iris Iris.BI Iris.ProofMode

variable {rT : Type} {GF : BundledGFunctors}
local bi (IProp GF)

/-- All component resources are retained together, indexed by their actual handles. -/
def owns : {n : ℕ} → (S : Fin n → Type) →
    (∀ i, Val rT → S i → IProp GF) → (Fin n → Val rT) → (∀ i, S i) → IProp GF
  | 0, _, _, _, _ => emp
  | _ + 1, S, O, handles, s => iprop(O 0 (handles 0) (s 0) ∗
      owns (fun i => S i.succ) (fun i => O i.succ) (Fin.tail handles) (Fin.tail s))

private theorem tail_update_zero {n : ℕ} {S : Fin (n + 1) → Type}
    (s : ∀ i, S i) (q : S 0) :
    Fin.tail (Function.update s 0 q) = Fin.tail s := by
  funext i
  simp [Fin.tail]

private theorem tail_update_succ {n : ℕ} {S : Fin (n + 1) → Type}
    (s : ∀ i, S i) (i : Fin n) (q : S i.succ) :
    Fin.tail (Function.update s i.succ q) = Function.update (Fin.tail s) i q := by
  funext j
  by_cases h : j = i
  · subst j
    simp [Fin.tail]
  · have h' : j.succ ≠ i.succ := fun heq => h (Fin.succ_inj.mp heq)
    simp [Fin.tail, Function.update_of_ne h, Function.update_of_ne h']

/-- Focus one component and retain a continuation that restores its refined state. -/
theorem access {n : ℕ} (S : Fin n → Type) (O : ∀ i, Val rT → S i → IProp GF)
    (handles : Fin n → Val rT) (s : ∀ i, S i) (i : Fin n) :
    owns S O handles s ⊢ iprop(O i (handles i) (s i) ∗
      ∀ q : S i, O i (handles i) q -∗ owns S O handles (Function.update s i q)) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · isimp only [owns]
      iintro ⟨Hhead, Htail⟩
      iframe Hhead
      iintro %q Hhead
      rw [tail_update_zero]
      isimp only [Function.update_self]
      iframe Hhead Htail
    · isimp only [owns]
      iintro ⟨Hhead, Htail⟩
      ihave ⟨Hi, Hrestore⟩ := ih (fun j => S j.succ) (fun j => O j.succ)
        (Fin.tail handles) (Fin.tail s) i $$ Htail
      isimp only [Fin.tail] at Hi
      iframe Hi
      iintro %q Hi
      rw [tail_update_succ]
      isimp only [Function.update_of_ne (Fin.succ_ne_zero i).symm]
      iframe Hhead
      have hh : Fin.tail handles i = handles i.succ := rfl
      isimp only [hh] at Hrestore
      iapply Hrestore $$ %q Hi

end ownership

end

end SampLib.LatentReal.PiModel
