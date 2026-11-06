import SampLib.PSRN.Support.LatentConditionedOracle
import SampLib.Latent.LatentViews

/-! # Coordinate views of an accepted shared latent world -/

open ProbLang

namespace SampLib.LatentReal.Conditioning

noncomputable section

section mathematics

open MeasureTheory

variable {Ω S : Type} [MeasurableSpace Ω]

/-- Restriction changes the shared posterior, retaining each coordinate's value and error. -/
def viewModel (world view : Model Ω S) (hworld : Model.SameWorld world view)
    (initial : S) (A : Set Ω) (hmass : world.posterior initial A ≠ 0) :
    Model Ω (Option (Accepted world initial A)) :=
  { model world initial A hmass with
    value := view.value
    measurable_value := view.measurable_value
    error := view.error
    error_tendsto := by
      intro s
      cases s with
      | none =>
        have h := view.error_tendsto initial
        rw [hworld.posterior_eq initial] at h
        have hac : Rejection.law (world.posterior initial) A hmass ≪ world.posterior initial :=
          (Measure.absolutelyContinuous_restrict
            (μ := world.posterior initial) (s := A)).smul_left _
        exact hac.ae_le h
      | some q =>
        simpa only [model, posterior, hworld.posterior_eq] using view.error_tendsto q.state }

theorem viewModel_sameWorld (world view : Model Ω S) (hworld : Model.SameWorld world view)
    (initial : S) (A : Set Ω) (hmass : world.posterior initial A ≠ 0) :
    Model.SameWorld (model world initial A hmass)
      (viewModel world view hworld initial A hmass) :=
  ⟨fun _ => rfl, fun _ _ => Iff.rfl⟩

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- Accepted coordinates retain the sole physical world, never a separated copy per handle. -/
def worldOwns (world : Model Ω S) (initial : S) (A : Set Ω) (P : S → IProp GF) :
    Option (Accepted world initial A) → IProp GF
  | none => iprop(⌜False⌝)
  | some q => P q.state

/-- Observing any coordinate preserves the previously established acceptance event. -/
theorem viewSpec (E : CoPset) (world view : Model Ω S) (hworld : Model.SameWorld world view)
    (initial : S) (A : Set Ω) (hmass : world.posterior initial A ≠ 0)
    (P : S → IProp GF) (handle : Val rT) (h : IsViewSpec E view P handle) :
    IsViewSpec E (viewModel world view hworld initial A hmass)
      (worldOwns world initial A P) handle where
  observe v s n F hF := by
    cases s with
    | none =>
      iintro ⟨Hstate, Hcredit⟩
      isimp only [ViewOwns, worldOwns] at Hstate
      icases Hstate with ⟨_, %hfalse⟩
      exact False.elim hfalse
    | some q =>
      iintro ⟨Hstate, Hcredit⟩
      isimp only [ViewOwns, worldOwns] at Hstate
      icases Hstate with ⟨%hv, Hstate⟩
      subst v
      isimp only [viewModel, model, posterior] at Hcredit
      isimp only [← hworld.posterior_eq q.state] at Hcredit
      iapply (h.wp q.state n F hF _) $$ Hstate Hcredit
      iintro %t %I %ht Hstate Hcredit
      rcases ht with ⟨hrefines, hencloses⟩
      have hwrefines := (hworld.refines_iff _ _).mp hrefines
      let q' : Accepted world initial A :=
        ⟨t, world.refines_trans q.refines_initial hwrefines,
          (world.absolutelyContinuous hwrefines).ae_le q.accepted⟩
      iexists some q', I
      isimp only [ViewOwns, worldOwns, viewModel, model, posterior]
      isimp only [hworld.posterior_eq t] at Hcredit
      iframe Hstate Hcredit
      ipureintro
      change True ∧ world.refines q.state t ∧
        (∀ᵐ x ∂world.posterior t,
          I.Contains (view.value x) ∧ I.upperReal - I.lowerReal ≤ view.error n x)
      refine ⟨trivial, hwrefines, ?_⟩
      simpa only [Model.Encloses, hworld.posterior_eq] using hencloses

end specification

end

end SampLib.LatentReal.Conditioning
