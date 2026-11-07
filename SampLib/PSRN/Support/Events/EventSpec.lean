import SampLib.PSRN.Support.Events.Conditioning

/-! # Tests of events of the same shared latent draw

An event callback returns a Boolean fact about the current latent value. Its
posterior credit retains the whole joint latent space, not just the Boolean's
unconditional marginal.
-/

open ProbLang
open MeasureTheory (Measure)
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- A conditional event test preserves the source oracle and the refined joint credit. -/
structure IsEventSpec (E : CoPset) (D : Model Ω S) (owns : Val rT → S → IProp GF)
    (A : Set Ω) [DecidablePred (· ∈ A)] (accept : Val rT) : Prop where
  measurable_event : MeasurableSet A
  spec (source : Val rT) (s : S) (G : Bool → Ω → ℝ≥0∞)
      (hG : ∀ b, Measurable (G b)) :
    iprop(owns source s ∗ ↯ (∫⁻ x, G (decide (x ∈ A)) x ∂D.posterior s)) ⊢
      tglWp E pl(&accept.fst &source.fst)
        (fun result : Val rT => iprop(∃ (b : Bool) (t : S),
          ⌜result = Val.bool b ∧ D.refines s t ∧
            ∀ᵐ x ∂D.posterior t, decide (x ∈ A) = b⌝ ∗
          owns source t ∗ ↯ (∫⁻ x, G b x ∂D.posterior t)))

namespace IsEventSpec

/-- Use a resolved event while framing unrelated caller resources. -/
theorem wp {E : CoPset} {D : Model Ω S} {owns : Val rT → S → IProp GF}
    {A : Set Ω} [DecidablePred (· ∈ A)] {accept : Val rT}
    (h : IsEventSpec E D owns A accept) (source : Val rT) (s : S)
    (G : Bool → Ω → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) (Φ : Val rT → IProp GF) :
    ⊢ owns source s -∗ ↯ (∫⁻ x, G (decide (x ∈ A)) x ∂D.posterior s) -∗
      (∀ (b : Bool) (t : S),
        ⌜D.refines s t ∧ ∀ᵐ x ∂D.posterior t, decide (x ∈ A) = b⌝ -∗
        owns source t -∗ ↯ (∫⁻ x, G b x ∂D.posterior t) -∗ Φ (Val.bool b)) -∗
      tglWp E pl(&accept.fst &source.fst) Φ := by
  iintro Hstate Hcredit Hcont
  iapply tglWp_wand
  isplitl [Hstate Hcredit]
  · iapply h.spec source s G hG
    iframe Hstate Hcredit
  iintro %result ⟨%b, %t, %ht, Hstate, Hcredit⟩
  rcases ht with ⟨rfl, hrefines, hevent⟩
  iapply Hcont $$ %b %t %⟨hrefines, hevent⟩ Hstate Hcredit

end IsEventSpec

end

end SampLib.LatentReal
