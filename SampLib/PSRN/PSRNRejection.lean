import SampLib.PSRN.Support.Events.RejectionKernel

/-! # Rejection preserving an accepted deferred real

The constructor uses the common latent rejection kernel. Its observation protocol
retains the accepted proposal's original oracle and conditional posterior.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNRejection

noncomputable section

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
    (hproposal : IsLatentDistSpec E pl(&proposal.fst #()) D initial rawOwns)
    (haccept : IsEventSpec E D rawOwns A accept) (F : Ω → ℝ≥0∞) (hF : Measurable F) :
    iprop(↯ (Rejection.credit (D.posterior initial) A hmass F)) ⊢
      tglWp E pl(&Occil.PSRN.newRejection &proposal.fst &accept.fst #())
        (fun v : Val rT => iprop(∃ q : Option (Conditioning.Accepted D initial A),
          ⌜(Conditioning.model D initial A hmass).refines none q⌝ ∗
          Conditioning.owns D initial A rawOwns v q ∗
          ↯ (∫⁻ x, F x ∂(Conditioning.model D initial A hmass).posterior q))) :=
  LatentRejectionKernel.twp_newRejection E D initial rawOwns A hmass proposal accept
    hproposal.payloadSpec haccept F hF

/-- A compositional conditional law, with the accepted candidate's private state retained. -/
theorem newRejection_latentDistSpec (E : CoPset) (D : Model Ω S) (initial : S)
    (rawOwns : Val rT → S → IProp GF) (A : Set Ω) [DecidablePred (· ∈ A)]
    (hmass : D.posterior initial A ≠ 0) (proposal accept : Val rT)
    (hproposal : IsLatentDistSpec E pl(&proposal.fst #()) D initial rawOwns)
    (haccept : IsEventSpec E D rawOwns A accept) :
    IsLatentDistSpec E pl(&Occil.PSRN.newRejection &proposal.fst &accept.fst #())
      (Conditioning.model D initial A hmass) none (Conditioning.owns D initial A rawOwns) where
  oracle := Conditioning.oracleSpec E D initial A hmass rawOwns hproposal.oracle
  spec F hF := twp_newRejection E D initial rawOwns A hmass proposal accept hproposal haccept F hF


end

end SampLib.PSRNRejection
