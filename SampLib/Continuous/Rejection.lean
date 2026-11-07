import SampLib.Templates
import SampLib.Core.Retry
import Samplers.Continuous.Rejection
import Metrology.Iris.LocalBI
import SampLib.Continuous.Laws.Rejection

/-!
# Rejection on a measurable acceptance set

The target law is the proposal law conditioned on acceptance. Auxiliary credit
is amplified only when the sampled proposal is rejected.
-/

open Set ProbLang
open scoped ENNReal NNReal

namespace SampLib.Rejection

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {α : Type _} [MeasurableSpace α]
local bi (IProp GF)

/-- CTE rejection spec for a verified proposal and deterministic acceptance test. -/
theorem twp_rejection (E : CoPset) (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure μ] (s : Set α) [DecidablePred (· ∈ s)]
    (hs : MeasurableSet s) (hmass : μ s ≠ 0) (encode : α → Val rT)
    (proposal accept : Val rT)
    (hproposal : IsDistSpec (GF := GF) E pl(&proposal.fst #()) μ encode)
    (haccept : ∀ x, ⊢ tglWp E pl(&accept.fst &(encode x).fst)
      (fun v : Val rT => iprop(⌜v = Val.bool (decide (x ∈ s))⌝)))
    (F : α → ℝ≥0∞) (hF : Measurable F) :
    ⊢ ↯ (credit μ s hmass F) -∗
      tglWp E pl(&Occil.rejection &proposal.fst &accept.fst #())
        (fun v : Val rT => iprop(∃ x : α, ⌜v = encode x⌝ ∗ ↯ (F x))) := by
  iapply Retry.twp_loop solve_not_value (one_lt_terminationFactor μ s hmass)
  iintro !> %ε %hε IH Hcredit
  twp_pures
  twp_bind pl(&proposal.fst #())
  ihave Hcredit := ErrorCredit.weaken (expectation_preservation μ s hs hmass F ε) $$ Hcredit
  iapply (hproposal.wp (kernel μ s hmass F ε) (measurable_kernel μ s hs hmass F hF ε) _)
    $$ Hcredit
  iintro %x Hcredit
  twp_pures
  twp_bind pl(&accept.fst &(encode x).fst)
  iapply tglWp_wand
  isplitl []
  · iapply haccept x
  iintro %v %hv
  subst v
  by_cases hx : x ∈ s
  · simp only [hx, decide_true]
    twp_pures
    iapply (tglWp_value_of_toVal (Val.toVal?_fst (encode x)))
    iexists x
    isimp only [kernel, ite_eq_left hx] at Hcredit
    iframe Hcredit
    itrivial
  · simp only [hx, decide_false]
    twp_pure
    isimp only [kernel, ite_eq_right hx] at Hcredit
    twp_bind pl(&Occil.rejection &proposal.fst &accept.fst #())
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply IH $$ Hcredit

/-- Typed conditional output law. -/
theorem rejection_distSpec (E : CoPset) (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure μ] (s : Set α) [DecidablePred (· ∈ s)]
    (hs : MeasurableSet s) (hmass : μ s ≠ 0) (encode : α → Val rT)
    (proposal accept : Val rT)
    (hproposal : IsDistSpec (GF := GF) E pl(&proposal.fst #()) μ encode)
    (haccept : ∀ x, ⊢ tglWp E pl(&accept.fst &(encode x).fst)
      (fun v : Val rT => iprop(⌜v = Val.bool (decide (x ∈ s))⌝))) :
    IsDistSpec (GF := GF) E pl(&Occil.rejection &proposal.fst &accept.fst #())
      (law μ s hmass) encode where
  spec F hF := wand_entails (twp_rejection E μ s hs hmass encode proposal accept
    hproposal haccept F hF)

end specification

end

end SampLib.Rejection
