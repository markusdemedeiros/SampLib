import SampLib.PSRN.Support.LatentRepresentedSpec

/-! # Observing a fixed represented view while retaining its shared world -/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.IsRepresentedViewSpec

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- The actual interval is returned with its enclosure and deterministic certificate. -/
theorem wp {E : CoPset} {D : Model Ω S} {R : Representation D}
    {P : S → IProp GF} {handle : Val rT} (h : IsRepresentedViewSpec E D R P handle)
    (s : S) (n : ℕ) (F : Ω → ℝ≥0∞) (hF : Measurable F) (Φ : Val rT → IProp GF) :
    ⊢ P s -∗ ↯ (∫⁻ x, F x ∂D.posterior s) -∗
      (∀ (t : S) (I : RationalInterval),
        ⌜D.refines s t ∧ D.Encloses t n I ∧ R.Observed t n I⌝ -∗
        P t -∗ ↯ (∫⁻ x, F x ∂D.posterior t) -∗ Φ (intervalVal I)) -∗
      tglWp E pl(&handle.fst #int (n : ℤ)) Φ := by
  iintro Hstate Hcredit Hcont
  iapply tglWp_wand
  isplitl [Hstate Hcredit]
  · iapply h.observe handle s n F hF
    isplitl [Hstate]
    · isimp only [ViewOwns]
      iframe Hstate
    iexact Hcredit
  iintro %result ⟨%t, %I, %hI, Hstate, Hcredit⟩
  rcases hI with ⟨rfl, hI⟩
  isimp only [ViewOwns] at Hstate
  icases Hstate with ⟨_, Hstate⟩
  iapply Hcont $$ %t %I %hI Hstate Hcredit

end

end SampLib.LatentReal.IsRepresentedViewSpec
