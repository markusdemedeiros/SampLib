import SampLib.PSRN.Support.LatentEventSpec
import SampLib.Latent.LatentPayloadSpec
import SampLib.PSRN.Support.LatentConditionedOracle
import Samplers.PSRN.Core

/-! # Rejection preserving an accepted deferred real

Each fresh proposal carries the full joint continuation kernel. An event test
refines that same candidate. Rejection funds amplification and discards only the
rejected private state; acceptance retains the actual oracle and its posterior.
-/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.LatentRejectionKernel

noncomputable section

section mathematics

open MeasureTheory

variable {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (A : Set Ω) [DecidablePred (· ∈ A)] (hmass : μ A ≠ 0)

/-- Accepted candidates carry output credit; rejected candidates carry a funded retry. -/
def branchCredit (F : Ω → ℝ≥0∞) (ε : ℝ≥0∞) (b : Bool) (x : Ω) : ℝ≥0∞ :=
  if b then F x else Rejection.credit μ A hmass F + Rejection.terminationFactor μ A * ε

omit [IsProbabilityMeasure μ] [DecidablePred (· ∈ A)] in
private theorem measurable_branchCredit (F : Ω → ℝ≥0∞) (hF : Measurable F) (ε : ℝ≥0∞)
    (b : Bool) : Measurable (branchCredit μ A hmass F ε b) := by
  cases b
  · exact measurable_const
  · exact hF

omit [IsProbabilityMeasure μ] in
private theorem measurable_kernel (hA : MeasurableSet A) (F : Ω → ℝ≥0∞)
    (hF : Measurable F) (ε : ℝ≥0∞) :
    Measurable (fun x => branchCredit μ A hmass F ε (decide (x ∈ A)) x) := by
  simpa only [branchCredit, decide_eq_true_eq] using
    Measurable.ite (p := fun x => x ∈ A) hA hF measurable_const

omit [IsProbabilityMeasure μ] [DecidablePred (· ∈ A)] in
private theorem return_credit (ν : Measure Ω) (F : Ω → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ x, branchCredit μ A hmass F ε true x ∂ν) = ∫⁻ x, F x ∂ν := by
  simp only [branchCredit, ite_true]

omit [IsProbabilityMeasure μ] [DecidablePred (· ∈ A)] in
private theorem retry_credit (ν : Measure Ω) [IsProbabilityMeasure ν]
    (F : Ω → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ x, branchCredit μ A hmass F ε false x ∂ν) =
      Rejection.credit μ A hmass F + Rejection.terminationFactor μ A * ε := by
  simp [branchCredit]

/-- The known rejection identity applies to the same latent event before its Boolean is observed. -/
theorem expectation_preservation (hA : MeasurableSet A) (F : Ω → ℝ≥0∞)
    (ε : ℝ≥0∞) :
    (∫⁻ x, branchCredit μ A hmass F ε (decide (x ∈ A)) x ∂μ) ≤
      Rejection.credit μ A hmass F + ε := by
  simpa only [branchCredit, decide_eq_true_eq, Rejection.kernel] using
    Rejection.expectation_preservation μ A hA hmass F ε

omit [DecidablePred (· ∈ A)] in
private theorem amplification (hmass : μ A ≠ 0) : 1 < Rejection.terminationFactor μ A := by
  exact lt_add_of_pos_right 1 (ENNReal.toNNReal_pos hmass (measure_ne_top μ A))

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open LatentReal

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- The actual retry loop returns an accepted oracle under the conditional law. -/
theorem twp_newRejection (E : CoPset) (D : Model Ω S) (initial : S)
    (rawOwns : Val rT → S → IProp GF) (A : Set Ω) [DecidablePred (· ∈ A)]
    (hmass : D.posterior initial A ≠ 0) (proposal accept : Val rT)
    (hproposal : IsLatentPayloadSpec E pl(&proposal.fst #()) D initial rawOwns)
    (haccept : IsEventSpec E D rawOwns A accept) (F : Ω → ℝ≥0∞) (hF : Measurable F) :
    iprop(↯ (Rejection.credit (D.posterior initial) A hmass F)) ⊢
      tglWp E pl(&Occil.PSRN.newRejection &proposal.fst &accept.fst #())
        (fun v : Val rT => iprop(∃ q : Option (Conditioning.Accepted D initial A),
          ⌜(Conditioning.model D initial A hmass).refines none q⌝ ∗
          Conditioning.owns D initial A rawOwns v q ∗
          ↯ (∫⁻ x, F x ∂(Conditioning.model D initial A hmass).posterior q))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε
    (amplification (D.posterior initial) A hmass) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  twp_pures
  twp_bind pl(&proposal.fst #())
  icombine Hcredit Hterm as Hcredit
  ihave Hcredit := ErrorCredit.weaken
    (expectation_preservation (D.posterior initial) A hmass haccept.measurable_event F ε)
    $$ Hcredit
  iapply (hproposal.wp _
    (measurable_kernel (D.posterior initial) A hmass haccept.measurable_event F hF ε) _)
    $$ Hcredit
  iintro %candidate %s %hs Hstate Hcredit
  twp_pures
  twp_bind pl(&accept.fst &candidate.fst)
  iapply (haccept.wp candidate s (branchCredit (D.posterior initial) A hmass F ε)
    (measurable_branchCredit (D.posterior initial) A hmass F hF ε) _)
    $$ Hstate Hcredit
  iintro %b %t %ht Hstate Hcredit
  rcases ht with ⟨hst, hevent⟩
  cases b
  · twp_pure
    isimp only [retry_credit] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    twp_bind pl(&Occil.PSRN.newRejection &proposal.fst &accept.fst #())
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply IH $$ Hterm Hcredit
  · twp_pures
    iapply (tglWp_value_of_toVal (Val.toVal?_fst candidate))
    have haccepted : ∀ᵐ x ∂D.posterior t, x ∈ A := by
      simpa only [decide_eq_true_eq] using hevent
    let q : Conditioning.Accepted D initial A := ⟨t, D.refines_trans hs hst, haccepted⟩
    iexists some q
    isimp only [Conditioning.owns, Conditioning.model, Conditioning.posterior]
    isimp only [return_credit] at Hcredit
    iframe Hstate Hcredit
    ipureintro
    trivial

/-- Constructor-only form, to be paired with a real or vector observation protocol. -/
theorem newRejection_payloadSpec (E : CoPset) (D : Model Ω S) (initial : S)
    (rawOwns : Val rT → S → IProp GF) (A : Set Ω) [DecidablePred (· ∈ A)]
    (hmass : D.posterior initial A ≠ 0) (proposal accept : Val rT)
    (hproposal : IsLatentPayloadSpec E pl(&proposal.fst #()) D initial rawOwns)
    (haccept : IsEventSpec E D rawOwns A accept) :
    IsLatentPayloadSpec E pl(&Occil.PSRN.newRejection &proposal.fst &accept.fst #())
      (Conditioning.model D initial A hmass) none (Conditioning.owns D initial A rawOwns) where
  spec F hF := twp_newRejection E D initial rawOwns A hmass proposal accept hproposal haccept F hF

end specification

end

end SampLib.LatentRejectionKernel
