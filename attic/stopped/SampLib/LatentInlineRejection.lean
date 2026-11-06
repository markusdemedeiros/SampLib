import SampLib.Latent.LatentConditionedOracle
import SampLib.LatentPositiveLikelihood
import SampLib.Latent.LatentCoinSpec
import SampLib.Latent.LatentPayloadSpec

/-! # Rejection loops written inline

A source may write `rec retry u := ...; if test then result else retry #()` instead of
calling `newRejection`. One unrolled attempt allocates a fresh proposal from the same
initial posterior, tests it on its joint world, and either returns an owned value or
re-enters the loop. An attempt is specified abstractly by its credit split; this file
supplies the amplification argument and the accepted posterior once.

Acceptance by an event keeps the conditioned world (`Conditioning.model`); acceptance by
a conditional coin keeps the likelihood-tilted world (`PositiveLikelihood.model`).
-/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.LatentReal.InlineRejection

noncomputable section

/-- Accepted attempts carry output credit; rejected attempts carry the retry budget `r`. -/
def branch {Ω : Type} (F : Ω → ℝ≥0∞) (r : ℝ≥0∞) (b : Bool) (x : Ω) : ℝ≥0∞ :=
  if b then F x else r

theorem measurable_branch {Ω : Type} [MeasurableSpace Ω] {F : Ω → ℝ≥0∞} (hF : Measurable F)
    (r : ℝ≥0∞) (b : Bool) : Measurable (branch F r b) := by
  cases b
  · exact measurable_const
  · exact hF

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- Amplified retry: an attempt that refunds `C + k ε` on rejection terminates. -/
theorem twp_retry (E : CoPset) (loop : Exp rT) (hloop : loop.toVal? = none)
    (Ψ : Val rT → IProp GF) (C : ℝ≥0∞) (k : ℝ≥0) (hk : 1 < k)
    (hattempt : ∀ ε : ℝ≥0∞,
      ⊢ (↯ (C + k * ε) -∗ tglWp E loop Ψ) -∗ ↯ (C + ε) -∗ tglWp E loop Ψ) :
    iprop(↯ C) ⊢ tglWp E loop Ψ := by
  iintro Hcredit
  iapply (twp_err_pos (e := loop) hloop)
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε hk $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  icombine Hcredit Hterm as Hcredit
  iapply hattempt ε $$ [IH] Hcredit
  iintro Hretry
  ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hretry
  iapply IH $$ Hterm Hcredit

section event

variable (E : CoPset) (loop : Exp rT) (D : Model Ω S) (initial : S) (A : Set Ω)
  [DecidablePred (· ∈ A)] (rawOwns : Val rT → S → IProp GF)

/-- One unrolled attempt accepting the event `A` of a fresh proposal from `D initial`. -/
structure IsEventAttempt : Prop where
  not_value : loop.toVal? = none
  measurable_event : MeasurableSet A
  attempt (F : Ω → ℝ≥0∞) (hF : Measurable F) (r : ℝ≥0∞) (Φ : Val rT → IProp GF) :
    ⊢ ↯ (∫⁻ x, branch F r (decide (x ∈ A)) x ∂D.posterior initial) -∗
      (↯ r -∗ tglWp E loop Φ) -∗
      (∀ (v : Val rT) (q : Conditioning.Accepted D initial A),
        rawOwns v q.state -∗ ↯ (∫⁻ x, F x ∂D.posterior q.state) -∗ Φ v) -∗
      tglWp E loop Φ

variable {E loop D initial A rawOwns}

/-- The loop returns an accepted proposal under the conditional law. -/
theorem IsEventAttempt.payloadSpec (h : IsEventAttempt E loop D initial A rawOwns)
    (hmass : D.posterior initial A ≠ 0) :
    IsLatentPayloadSpec E loop (Conditioning.model D initial A hmass) none
      (Conditioning.owns D initial A rawOwns) where
  spec F hF := by
    apply twp_retry E loop h.not_value _ (Rejection.credit (D.posterior initial) A hmass F)
      (Rejection.terminationFactor (D.posterior initial) A) (lt_add_of_pos_right 1 (ENNReal.toNNReal_pos hmass (MeasureTheory.measure_ne_top _ A)))
    intro ε
    iintro Hretry Hcredit
    ihave Hcredit := ErrorCredit.weaken
      (Rejection.expectation_preservation (D.posterior initial) A h.measurable_event hmass F ε)
      $$ Hcredit
    iapply h.attempt F hF _ _ $$ [Hcredit] Hretry
    · simp only [Rejection.kernel, branch, decide_eq_true_eq]
      iexact Hcredit
    iintro %v %q Hstate Hcredit
    iexists some q
    isimp only [Conditioning.owns, Conditioning.model, Conditioning.posterior]
    iframe Hstate Hcredit
    ipureintro
    trivial

/-- With the proposal's observation protocol, the accepted oracle is a latent real. -/
theorem IsEventAttempt.latentDistSpec (h : IsEventAttempt E loop D initial A rawOwns)
    (hmass : D.posterior initial A ≠ 0) (horacle : IsOracleSpec E D rawOwns) :
    IsLatentDistSpec E loop (Conditioning.model D initial A hmass) none
      (Conditioning.owns D initial A rawOwns) where
  oracle := Conditioning.oracleSpec E D initial A hmass rawOwns horacle
  spec := (h.payloadSpec hmass).spec

end event

section likelihood

variable (E : CoPset) (loop : Exp rT) (D : Model Ω S) (initial : S) (φ : Ω → unitInterval)
  (rawOwns : Val rT → S → IProp GF)

/-- One unrolled attempt accepting a fresh proposal with conditional probability `φ`. -/
structure IsCoinAttempt : Prop where
  not_value : loop.toVal? = none
  measurable_bias : Measurable φ
  attempt (F : Ω → ℝ≥0∞) (hF : Measurable F) (r : ℝ≥0∞) (Φ : Val rT → IProp GF) :
    ⊢ ↯ (LatentCoin.credit D initial φ (branch F r)) -∗
      (↯ r -∗ tglWp E loop Φ) -∗
      (∀ (v : Val rT) (t : S), ⌜D.refines initial t⌝ -∗
        rawOwns v t -∗ ↯ (∫⁻ x, F x ∂D.posterior t) -∗ Φ v) -∗
      tglWp E loop Φ

variable {E loop D initial φ rawOwns}

/-- The loop returns an accepted proposal under the normalized likelihood tilt. -/
theorem IsCoinAttempt.payloadSpec (h : IsCoinAttempt E loop D initial φ rawOwns)
    (hpos : ∀ᵐ x ∂D.posterior initial, 0 < (φ x : ℝ))
    (hmass : AcceptedProposal.mass (D.posterior initial) φ ≠ 0) :
    IsLatentPayloadSpec E loop (PositiveLikelihood.model D initial φ h.measurable_bias hpos hmass)
      none (PositiveLikelihood.owns D initial rawOwns) where
  spec F hF := by
    apply twp_retry E loop h.not_value _
      (AcceptedProposal.credit (D.posterior initial) φ hmass F) _
      (AcceptedProposal.one_lt_factor (D.posterior initial) φ hmass)
    intro ε
    iintro Hretry Hcredit
    ihave Hcredit := ErrorCredit.weaken
      (AcceptedProposal.expectation_preservation (D.posterior initial) φ h.measurable_bias
        hmass F hF ε) $$ Hcredit
    iapply h.attempt F hF _ _ $$ [Hcredit] Hretry
    · simp only [AcceptedProposal.kernel, AcceptedProposal.weight,
        AcceptedProposal.rejectedWeight, LatentCoin.credit, LatentCoin.kernel,
        RealCoin.credit, RealCoin.pmf, branch, ite_true, Bool.false_eq_true, ite_false]
      iexact Hcredit
    iintro %v %t %ht Hstate Hcredit
    iexists some ⟨t, ht⟩
    isimp only [PositiveLikelihood.owns, PositiveLikelihood.model,
      PositiveLikelihood.posterior]
    iframe Hstate Hcredit
    ipureintro
    trivial

/-- With the proposal's observation protocol, the accepted oracle is a latent real. -/
theorem IsCoinAttempt.latentDistSpec (h : IsCoinAttempt E loop D initial φ rawOwns)
    (hpos : ∀ᵐ x ∂D.posterior initial, 0 < (φ x : ℝ))
    (hmass : AcceptedProposal.mass (D.posterior initial) φ ≠ 0)
    (horacle : IsOracleSpec E D rawOwns) :
    IsLatentDistSpec E loop (PositiveLikelihood.model D initial φ h.measurable_bias hpos hmass)
      none (PositiveLikelihood.owns D initial rawOwns) where
  oracle := PositiveLikelihood.oracleSpec E D initial φ h.measurable_bias hpos hmass rawOwns
    horacle
  spec := (h.payloadSpec hpos hmass).spec

end likelihood

end specification

end

end SampLib.LatentReal.InlineRejection
