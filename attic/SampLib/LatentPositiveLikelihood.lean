import SampLib.Latent.LatentSpec
import SampLib.Latent.LatentMeasuredError
import SampLib.Common.Laws.AcceptedProposal

/-! # A latent world accepted with an almost-everywhere positive likelihood

The initial law is the normalized likelihood tilt of the proposal. Accepted
oracles retain their actual source cache and its posterior; positivity transports
all initial null-set facts to those refined states.
-/

open ProbLang
open MeasureTheory (Measure IsProbabilityMeasure)

namespace SampLib.LatentReal.PositiveLikelihood

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω]

/-- An accepted proposal retains a source state reachable from initialization. -/
abbrev Refined (D : Model Ω S) (initial : S) := {s : S // D.refines initial s}

section mathematics

open MeasureTheory

variable (D : Model Ω S) (initial : S) (φ : Ω → unitInterval)
  (hφ : Measurable φ) (hpos : ∀ᵐ x ∂D.posterior initial, 0 < (φ x : ℝ))
  (hmass : AcceptedProposal.mass (D.posterior initial) φ ≠ 0)

def posterior : Option (Refined D initial) → Measure Ω
  | none => AcceptedProposal.law (D.posterior initial) φ hmass
  | some q => D.posterior q.val

instance (q : Option (Refined D initial)) :
    IsProbabilityMeasure (posterior D initial φ hmass q) := by
  cases q <;> dsimp [posterior] <;> infer_instance

/-- An accepted oracle never returns to the pre-construction state. -/
def Refines : Option (Refined D initial) → Option (Refined D initial) → Prop
  | none, _ => True
  | some _, none => False
  | some q, some r => D.refines q.val r.val

include hφ hpos in
private theorem source_absolutelyContinuous :
    D.posterior initial ≪ AcceptedProposal.law (D.posterior initial) φ hmass := by
  have hweight : ∀ᵐ x ∂D.posterior initial, AcceptedProposal.weight φ x ≠ 0 :=
    hpos.mono fun _ hx => (ENNReal.ofReal_pos.mpr hx).ne'
  exact (withDensity_absolutelyContinuous'
    (AcceptedProposal.measurable_weight φ hφ).aemeasurable hweight).smul_right
      (ENNReal.inv_ne_zero.mpr (AcceptedProposal.mass_ne_top (D.posterior initial) φ))

private theorem initial_absolutelyContinuous :
    AcceptedProposal.law (D.posterior initial) φ hmass ≪ D.posterior initial :=
  (withDensity_absolutelyContinuous _ _).smul_left _

include hφ hpos in
/-- The accepted real uses the same projection and interval error as its source. -/
def model : Model Ω (Option (Refined D initial)) where
  posterior := posterior D initial φ hmass
  probability _ := inferInstance
  value := D.value
  measurable_value := D.measurable_value
  refines := Refines D initial
  refines_refl q := by
    cases q with
    | none => trivial
    | some q => exact D.refines_refl q.val
  refines_trans := by
    intro q r t hqr hrt
    cases q <;> cases r <;> cases t <;> simp_all [Refines]
    exact D.refines_trans hqr hrt
  absolutelyContinuous := by
    intro q r hqr
    cases q with
    | none =>
      cases r with
      | none => exact Measure.AbsolutelyContinuous.rfl
      | some r =>
        exact (D.absolutelyContinuous r.property).trans
          (source_absolutelyContinuous D initial φ hφ hpos hmass)
    | some q =>
      cases r with
      | none => exact False.elim hqr
      | some r => exact D.absolutelyContinuous hqr
  error := D.error
  error_tendsto q := by
    cases q with
    | none =>
      exact (initial_absolutelyContinuous D initial φ hmass).ae_le (D.error_tendsto initial)
    | some q => exact D.error_tendsto q.val

/-- Conditioning does not change the source's measurable error functions. -/
theorem measurableError (hD : D.MeasurableError) :
    (model D initial φ hφ hpos hmass).MeasurableError := hD

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The pre-construction state is not observable; accepted states own the actual source. -/
def owns (D : Model Ω S) (initial : S) (rawOwns : Val rT → S → IProp GF)
    (v : Val rT) : Option (Refined D initial) → IProp GF
  | none => iprop(⌜False⌝)
  | some q => rawOwns v q.val

/-- All later observations retain the already accepted source and its refined state. -/
theorem oracleSpec (E : CoPset) (D : Model Ω S) (initial : S) (φ : Ω → unitInterval)
    (hφ : Measurable φ) (hpos : ∀ᵐ x ∂D.posterior initial, 0 < (φ x : ℝ))
    (hmass : AcceptedProposal.mass (D.posterior initial) φ ≠ 0)
    (rawOwns : Val rT → S → IProp GF) (h : IsOracleSpec E D rawOwns) :
    IsOracleSpec E (model D initial φ hφ hpos hmass) (owns D initial rawOwns) where
  observe v s n F hF := by
    cases s with
    | none =>
      iintro ⟨Hstate, _⟩
      isimp only [owns] at Hstate
      icases Hstate with %hfalse
      exact hfalse.elim
    | some q =>
      iintro Hstate
      isimp only [owns, model, posterior] at Hstate
      iapply tglWp_wand
      isplitl [Hstate]
      · iapply h.observe v q.val n F hF $$ Hstate
      iintro %result ⟨%t, %I, %ht, Hstate, Hcredit⟩
      rcases ht with ⟨rfl, hrefines, hencloses⟩
      let q' : Refined D initial := ⟨t, D.refines_trans q.property hrefines⟩
      iexists some q', I
      isimp only [owns, model, posterior]
      iframe Hstate Hcredit
      ipureintro
      exact ⟨trivial, hrefines, hencloses⟩

end specification

end

end SampLib.LatentReal.PositiveLikelihood
