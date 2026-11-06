import SampLib.PSRN.Support.LatentRepresentedReciprocal
import SampLib.PSRN.Support.LatentRepresentedStateInvariant

/-! # A fixed reciprocal view of the same owned latent world -/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.RepresentedReciprocalView

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω]

def Nonzero (D : Model Ω S) (s : S) : Prop := ∀ᵐ x ∂D.posterior s, D.value x ≠ 0

theorem nonzero_refines (D : Model Ω S) {s t : S} (h : D.refines s t) :
    Nonzero D s → Nonzero D t := fun hne => (D.absolutelyContinuous h).ae_le hne

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [MeasurableSpace rT] [LawfulProbLangℝ rT] [ProbLangDist rT]
  [ProbLangFFI rT] [ProbLangObs rT] in
/-- The existential source is the same fixed handle, with only pure nonzero metadata added. -/
theorem owns_fixed (D : Model Ω S) (P : S → IProp GF) (handle v : Val rT) (s : S) :
    RepresentedReciprocal.owns D (ViewOwns handle P) v s ⊣⊢
      ViewOwns (RepresentedReciprocal.Program.value handle) (withInvariant (Nonzero D) P) v s := by
  constructor
  · iintro Hstate
    isimp only [RepresentedReciprocal.owns, ViewOwns] at Hstate
    icases Hstate with ⟨%source, %hv, %hs, Hstate⟩
    subst source
    rcases hv with ⟨rfl, hn⟩
    isimp only [ViewOwns, withInvariant]
    isplitl []
    · ipureintro
      trivial
    isplitl []
    · ipureintro
      exact hn
    iexact Hstate
  · iintro Hstate
    isimp only [ViewOwns, withInvariant] at Hstate
    icases Hstate with ⟨%hv, %hn, Hstate⟩
    subst v
    isimp only [RepresentedReciprocal.owns]
    iexists handle
    isplitl []
    · ipureintro
      exact ⟨rfl, hn⟩
    isimp only [ViewOwns]
    iframe Hstate

/-- Constructing a reciprocal only captures the handle and retains its current invariant. -/
theorem twp_constructor (E : CoPset) (D : Model Ω S) (P : S → IProp GF)
    (handle : Val rT) (s : S) :
    withInvariant (Nonzero D) P s ⊢
      tglWp E pl(&Occil.PSRN.reciprocal &handle.fst)
        (fun v => ViewOwns (RepresentedReciprocal.Program.value handle)
          (withInvariant (Nonzero D) P) v s) := by
  iintro Hstate
  iapply RepresentedReciprocal.Program.twp_constructor E handle _
  isimp only [ViewOwns]
  iframe Hstate

/-- Adaptive inverse reads preserve the original physical ownership and the full joint credit. -/
theorem viewSpec (E : CoPset) (D : Model Ω S) (R : Representation D)
    (P : S → IProp GF) (handle : Val rT) (h : IsRepresentedViewSpec E D R P handle) :
    IsRepresentedViewSpec E (RepresentedReciprocal.model D R)
      (RepresentedReciprocal.representation D R) (withInvariant (Nonzero D) P)
      (RepresentedReciprocal.Program.value handle) where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    ihave Hstate := (owns_fixed D P handle v s).2 $$ Hstate
    iapply tglWp_wand
    isplitl [Hstate Hcredit]
    · iapply (RepresentedReciprocal.oracleSpec E D R (ViewOwns handle P) h).observe v s n F hF
      iframe Hstate Hcredit
    iintro %result ⟨%t, %I, %hI, Hstate, Hcredit⟩
    iexists t, I
    iframe Hcredit
    isplitl []
    · ipureintro
      exact hI
    iapply (owns_fixed D P handle v t).1 $$ Hstate

end specification

end

end SampLib.LatentReal.RepresentedReciprocalView
