import SampLib.LatentCoinSpec
import SampLib.LatentPayloadSpec
import SampLib.LatentPositiveLikelihood
import Samplers.PSRN.Core

/-! # Rejection by a conditional coin over an owned latent proposal

The coin preserves the proposal's full joint continuation kernel. Almost-everywhere
positive acceptance permits retaining the accepted proposal's actual cache under
the normalized likelihood law.
-/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.LatentReal.LikelihoodRejection

noncomputable section

section mathematics

open MeasureTheory

variable {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (φ : Ω → unitInterval) (hmass : AcceptedProposal.mass μ φ ≠ 0)

/-- A successful coin returns the proposal; a failed coin pays for the next attempt. -/
def branchCredit (F : Ω → ℝ≥0∞) (ε : ℝ≥0∞) (b : Bool) (x : Ω) : ℝ≥0∞ :=
  if b then F x else AcceptedProposal.credit μ φ hmass F + AcceptedProposal.factor μ φ * ε

omit [IsProbabilityMeasure μ] in
private theorem measurable_branchCredit (F : Ω → ℝ≥0∞) (hF : Measurable F) (ε : ℝ≥0∞)
    (b : Bool) : Measurable (branchCredit μ φ hmass F ε b) := by
  cases b
  · exact measurable_const
  · exact hF

omit [IsProbabilityMeasure μ] in
private theorem return_credit (ν : Measure Ω) (F : Ω → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ x, branchCredit μ φ hmass F ε true x ∂ν) = ∫⁻ x, F x ∂ν := by
  simp only [branchCredit, ite_true]

omit [IsProbabilityMeasure μ] in
private theorem retry_credit (ν : Measure Ω) [IsProbabilityMeasure ν]
    (F : Ω → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ x, branchCredit μ φ hmass F ε false x ∂ν) =
      AcceptedProposal.credit μ φ hmass F + AcceptedProposal.factor μ φ * ε := by
  simp [branchCredit]

/-- Weighting the same latent proposal preserves its credit and funds amplification. -/
theorem expectation_preservation (hφ : Measurable φ) (F : Ω → ℝ≥0∞)
    (hF : Measurable F) (ε : ℝ≥0∞) :
    (∫⁻ x, LatentCoin.kernel φ (branchCredit μ φ hmass F ε) x ∂μ) ≤
      AcceptedProposal.credit μ φ hmass F + ε := by
  simpa only [LatentCoin.kernel, RealCoin.credit, RealCoin.pmf, branchCredit,
    ite_true, Bool.false_eq_true, ite_false, AcceptedProposal.kernel,
    AcceptedProposal.weight, AcceptedProposal.rejectedWeight] using
    AcceptedProposal.expectation_preservation μ φ hφ hmass F hF ε

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- The actual rejection loop retains the accepted source state under its likelihood tilt. -/
theorem twp_newRejection (E : CoPset) (D : Model Ω S) (initial : S)
    (rawOwns : Val rT → S → IProp GF) (φ : Ω → unitInterval)
    (hpos : ∀ᵐ x ∂D.posterior initial, 0 < (φ x : ℝ))
    (hmass : AcceptedProposal.mass (D.posterior initial) φ ≠ 0) (proposal accept : Val rT)
    (hproposal : IsLatentPayloadSpec E pl(&proposal.fst #()) D initial rawOwns)
    (haccept : IsLatentCoinProgramSpec E D rawOwns φ
      (fun candidate => pl(&accept.fst &candidate.fst)))
    (F : Ω → ℝ≥0∞) (hF : Measurable F) :
    iprop(↯ (AcceptedProposal.credit (D.posterior initial) φ hmass F)) ⊢
      tglWp E pl(&Occil.PSRN.newRejection &proposal.fst &accept.fst #())
        (fun v : Val rT => iprop(∃ q : Option (PositiveLikelihood.Refined D initial),
          ⌜(PositiveLikelihood.model D initial φ
            haccept.measurable_bias hpos hmass).refines none q⌝ ∗
          PositiveLikelihood.owns D initial rawOwns v q ∗
          ↯ (∫⁻ x, F x ∂(PositiveLikelihood.model D initial φ
            haccept.measurable_bias hpos hmass).posterior q))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε
    (AcceptedProposal.one_lt_factor (D.posterior initial) φ hmass) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  twp_pures
  twp_bind pl(&proposal.fst #())
  icombine Hcredit Hterm as Hcredit
  ihave Hcredit := ErrorCredit.weaken
    (expectation_preservation (D.posterior initial) φ hmass haccept.measurable_bias F hF ε)
    $$ Hcredit
  iapply (hproposal.wp _
    (LatentCoin.measurable_kernel haccept.measurable_bias
      (measurable_branchCredit (D.posterior initial) φ hmass F hF ε)) _)
    $$ Hcredit
  iintro %candidate %s %hs Hstate Hcredit
  twp_pures
  twp_bind pl(&accept.fst &candidate.fst)
  have hcall (Φ : Val rT → IProp GF) :=
    haccept.wp candidate s (branchCredit (D.posterior initial) φ hmass F ε)
      (measurable_branchCredit (D.posterior initial) φ hmass F hF ε) Φ
  simp only [LatentCoin.credit] at hcall
  iapply hcall _ $$ Hstate Hcredit
  iintro %b %t %ht Hstate Hcredit
  cases b
  · twp_pure
    isimp only [retry_credit] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    twp_bind pl(&Occil.PSRN.newRejection &proposal.fst &accept.fst #())
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply IH $$ Hterm Hcredit
  · twp_pures
    iapply (tglWp_value_of_toVal (Val.toVal?_fst candidate))
    let q : PositiveLikelihood.Refined D initial := ⟨t, D.refines_trans hs ht⟩
    iexists some q
    isimp only [PositiveLikelihood.owns, PositiveLikelihood.model, PositiveLikelihood.posterior]
    isimp only [return_credit] at Hcredit
    iframe Hstate Hcredit
    ipureintro
    trivial

/-- Constructor-only form, suitable for real, pair, or vector observation protocols. -/
theorem newRejection_payloadSpec (E : CoPset) (D : Model Ω S) (initial : S)
    (rawOwns : Val rT → S → IProp GF) (φ : Ω → unitInterval)
    (hpos : ∀ᵐ x ∂D.posterior initial, 0 < (φ x : ℝ))
    (hmass : AcceptedProposal.mass (D.posterior initial) φ ≠ 0) (proposal accept : Val rT)
    (hproposal : IsLatentPayloadSpec E pl(&proposal.fst #()) D initial rawOwns)
    (haccept : IsLatentCoinProgramSpec E D rawOwns φ
      (fun candidate => pl(&accept.fst &candidate.fst))) :
    IsLatentPayloadSpec E pl(&Occil.PSRN.newRejection &proposal.fst &accept.fst #())
      (PositiveLikelihood.model D initial φ haccept.measurable_bias hpos hmass) none
      (PositiveLikelihood.owns D initial rawOwns) where
  spec F hF := twp_newRejection E D initial rawOwns φ hpos hmass proposal accept
    hproposal haccept F hF

/-- Deferred-real rejection pairs the constructor with the retained source observer. -/
theorem newRejection_latentDistSpec (E : CoPset) (D : Model Ω S) (initial : S)
    (rawOwns : Val rT → S → IProp GF) (φ : Ω → unitInterval)
    (hpos : ∀ᵐ x ∂D.posterior initial, 0 < (φ x : ℝ))
    (hmass : AcceptedProposal.mass (D.posterior initial) φ ≠ 0) (proposal accept : Val rT)
    (hproposal : IsLatentDistSpec E pl(&proposal.fst #()) D initial rawOwns)
    (haccept : IsLatentCoinProgramSpec E D rawOwns φ
      (fun candidate => pl(&accept.fst &candidate.fst))) :
    IsLatentDistSpec E pl(&Occil.PSRN.newRejection &proposal.fst &accept.fst #())
      (PositiveLikelihood.model D initial φ haccept.measurable_bias hpos hmass) none
      (PositiveLikelihood.owns D initial rawOwns) where
  spec F hF := twp_newRejection E D initial rawOwns φ hpos hmass proposal accept
    hproposal.payloadSpec haccept F hF
  oracle := PositiveLikelihood.oracleSpec E D initial φ haccept.measurable_bias hpos hmass
    rawOwns hproposal.oracle

end specification

end

end SampLib.LatentReal.LikelihoodRejection
