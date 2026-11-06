import SampLib.Latent.LatentSpec

/-! # Constructor credit for deferred payloads

This interface records construction only. A real or vector sampler specification
must additionally supply the observation protocol for the actual returned value.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- Construction preserves joint posterior credit and the payload's owned state. -/
structure IsLatentPayloadSpec (E : CoPset) (e : Exp rT) (D : Model Ω S) (initial : S)
    (owns : Val rT → S → IProp GF) : Prop where
  spec (F : Ω → ℝ≥0∞) (hF : Measurable F) :
    iprop(↯ (∫⁻ x, F x ∂D.posterior initial)) ⊢
      tglWp E e (fun v : Val rT => iprop(∃ t : S,
        ⌜D.refines initial t⌝ ∗ owns v t ∗ ↯ (∫⁻ x, F x ∂D.posterior t)))

namespace IsLatentPayloadSpec

/-- Pass the constructed payload and its posterior to an arbitrary caller. -/
theorem wp {E : CoPset} {e : Exp rT} {D : Model Ω S} {initial : S}
    {owns : Val rT → S → IProp GF} (h : IsLatentPayloadSpec E e D initial owns)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) (Φ : Val rT → IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂D.posterior initial) -∗
      (∀ (v : Val rT) (t : S), ⌜D.refines initial t⌝ -∗ owns v t -∗
        ↯ (∫⁻ x, F x ∂D.posterior t) -∗ Φ v) -∗ tglWp E e Φ := by
  iintro Hcredit Hcont
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply h.spec F hF $$ Hcredit
  iintro %v ⟨%t, %ht, Hstate, Hcredit⟩
  iapply Hcont $$ %v %t %ht Hstate Hcredit

end IsLatentPayloadSpec

/-- The constructor component of a fully observable lazy-real specification. -/
theorem IsLatentDistSpec.payloadSpec {E : CoPset} {e : Exp rT} {D : Model Ω S} {initial : S}
    {owns : Val rT → S → IProp GF} (h : IsLatentDistSpec E e D initial owns) :
    IsLatentPayloadSpec E e D initial owns where
  spec := h.spec

end

end SampLib.LatentReal
