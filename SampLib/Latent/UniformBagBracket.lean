import SampLib.Latent.UniformBagLess
import SampLib.Common.Laws.DyadicRefinement

/-! # Two comparisons with one cached uniform

Each continuation receives the original cache, its refined posterior credit,
and the comparison facts learned along that branch.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.UniformBag

noncomputable section

theorem uniformBagLess_lc {rT : Type} :
    (Occil.uniformBagLess : Exp rT).IsLocallyClosed := by is_lc

theorem uniformBagLess_fv {rT : Type} : (Occil.uniformBagLess : Exp rT).fv = ∅ := by
  simp [Occil.uniformBagLess, Occil.uniformBagStep, Occil.newUniformBag,
    Occil.fairCoin, Exp.fv]

@[simp] theorem uniformBagLess_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.uniformBagLess = Occil.uniformBagLess :=
  (Exp.open_lc k e _ uniformBagLess_lc).symm

@[simp] theorem uniformBagLess_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.uniformBagLess : Exp rT) = Occil.uniformBagLess :=
  Exp.closeRec_fresh x _ k (by simp [uniformBagLess_fv])

/-- Test the lower threshold, then the upper threshold of the same latent uniform. -/
def bracket {rT : Type} (l : Loc) (lower lowerDen upper upperDen : ℤ)
    (yes no retry : Exp rT) : Exp rT :=
  .cond pl(&Occil.uniformBagLess #loc l #int lower #int lowerDen) yes
    (.cond pl(&Occil.uniformBagLess #loc l #int upper #int upperDen) retry no)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Shared-uniform bracketing composes arbitrary caller continuations. -/
theorem twp_bracket (E : CoPset) (l : Loc) (p : List Bool) (lower lowerDen upper upperDen : ℤ)
    (hl : 0 < lowerDen) (hu : 0 < upperDen) (G : ℝ → ℝ≥0∞) (hG : Measurable G)
    (yes no retry : Exp rT) (Φ : Val rT → IProp GF)
    (hyes : ∀ q : List Bool, p <+: q →
      DyadicPosterior.resolves q ((lower : ℝ) / lowerDen) true →
      iprop(owns l q ∗ ↯ (DyadicPosterior.credit q G)) ⊢ tglWp E yes Φ)
    (hno : ∀ q : List Bool, p <+: q →
      DyadicPosterior.resolves q ((lower : ℝ) / lowerDen) false →
      DyadicPosterior.resolves q ((upper : ℝ) / upperDen) false →
      iprop(owns l q ∗ ↯ (DyadicPosterior.credit q G)) ⊢ tglWp E no Φ)
    (hretry : ∀ q : List Bool, p <+: q →
      DyadicPosterior.resolves q ((lower : ℝ) / lowerDen) false →
      DyadicPosterior.resolves q ((upper : ℝ) / upperDen) true →
      iprop(owns l q ∗ ↯ (DyadicPosterior.credit q G)) ⊢ tglWp E retry Φ) :
    iprop(owns l p ∗ ↯ (DyadicPosterior.credit p G)) ⊢
      tglWp E (bracket l lower lowerDen upper upperDen yes no retry) Φ := by
  iintro ⟨Hbag, Hcredit⟩
  isimp only [bracket]
  twp_bind pl(&Occil.uniformBagLess #loc l #int lower #int lowerDen)
  iapply tglWp_wand
  isplitl [Hbag Hcredit]
  · iapply twp_uniformBagLess E l p lower lowerDen hl G hG
    iframe Hbag Hcredit
  iintro %v Hnext
  isimp only [lessPost] at Hnext
  ihave ⟨%b, %q, %hq, Hbag, Hcredit⟩ := Hnext
  rcases hq with ⟨rfl, hprefix, hlow⟩
  cases b
  · twp_pure
    twp_bind pl(&Occil.uniformBagLess #loc l #int upper #int upperDen)
    iapply tglWp_wand
    isplitl [Hbag Hcredit]
    · iapply twp_uniformBagLess E l q upper upperDen hu G hG
      iframe Hbag Hcredit
    iintro %v Hnext
    isimp only [lessPost] at Hnext
    ihave ⟨%b, %r, %hr, Hbag, Hcredit⟩ := Hnext
    rcases hr with ⟨rfl, hnext, hupp⟩
    have hprefix' := hprefix.trans hnext
    have hlow' := DyadicPosterior.resolves_refines hnext hlow
    cases b
    · twp_pure
      iapply hno r hprefix' hlow' hupp
      iframe Hbag Hcredit
    · twp_pure
      iapply hretry r hprefix' hlow' hupp
      iframe Hbag Hcredit
  · twp_pure
    iapply hyes q hprefix hlow
    iframe Hbag Hcredit

end specification

end

end SampLib.UniformBag
