import SampLib.PSRN.Support.Events.Conditioning

/-! # Observing an already accepted latent oracle -/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.Conditioning

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- Initialization is not an observable oracle; accepted states retain their private resources. -/
def owns (D : Model Ω S) (initial : S) (A : Set Ω)
    (rawOwns : Val rT → S → IProp GF) (v : Val rT) :
    Option (Accepted D initial A) → IProp GF
  | none => iprop(⌜False⌝)
  | some q => rawOwns v q.state

/-- Future observations preserve the previously established acceptance event. -/
theorem oracleSpec (E : CoPset) (D : Model Ω S) (initial : S) (A : Set Ω)
    (hmass : D.posterior initial A ≠ 0) (rawOwns : Val rT → S → IProp GF)
    (h : IsOracleSpec E D rawOwns) :
    IsOracleSpec E (model D initial A hmass) (owns D initial A rawOwns) where
  observe v s n F hF := by
    cases s with
    | none =>
      iintro ⟨Hstate, Hcredit⟩
      isimp only [owns] at Hstate
      ihave %hfalse := Hstate
      exact False.elim hfalse
    | some q =>
      have hread := h.observe v q.state n F hF
      iintro Hstate
      isimp only [owns, model, posterior] at Hstate
      iapply tglWp_wand
      isplitl [Hstate]
      · iapply hread $$ Hstate
      iintro %result ⟨%t, %I, %ht, Hstate, Hcredit⟩
      rcases ht with ⟨rfl, hrefines, hencloses⟩
      let q' : Accepted D initial A :=
        ⟨t, D.refines_trans q.refines_initial hrefines,
          (D.absolutelyContinuous hrefines).ae_le q.accepted⟩
      iexists some q', I
      isimp only [owns, model, posterior]
      iframe Hstate Hcredit
      ipureintro
      exact ⟨trivial, hrefines, hencloses⟩

end

end SampLib.LatentReal.Conditioning
