import SampLib.Latent.LatentSpec

/-! # Several observable views of one shared latent world

Each handle consumes and returns the same physical ownership. Sequentially
reading two handles therefore permits aliases and shared normalizers without
duplicating the heap resource or factoring their mathematical marginal laws.
-/

open ProbLang
open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

namespace Model

variable {Ω S : Type} [MeasurableSpace Ω]

/-- Two real projections may differ while sharing posteriors and physical refinements. -/
structure SameWorld (left right : Model Ω S) : Prop where
  posterior_eq : ∀ s, right.posterior s = left.posterior s
  refines_iff : ∀ s t, right.refines s t ↔ left.refines s t

namespace SameWorld

variable {left right : Model Ω S}

theorem refl (D : Model Ω S) : SameWorld D D := ⟨fun _ => rfl, fun _ _ => Iff.rfl⟩

end SameWorld

end Model

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- A fixed handle exposes a projection while retaining the common physical state. -/
def ViewOwns (handle : Val rT) (P : S → IProp GF) (v : Val rT) (s : S) : IProp GF :=
  iprop(⌜v = handle⌝ ∗ P s)

/-- All views of one world may use the same ownership predicate `P`. -/
def IsViewSpec (E : CoPset) (D : Model Ω S) (P : S → IProp GF) (handle : Val rT) : Prop :=
  IsOracleSpec E D (ViewOwns handle P)

namespace IsViewSpec

/-- Observe one projection, returning the very same common ownership to the continuation. -/
theorem wp {E : CoPset} {D : Model Ω S} {P : S → IProp GF} {handle : Val rT}
    (h : IsViewSpec E D P handle) (s : S) (n : ℕ) (F : Ω → ℝ≥0∞) (hF : Measurable F)
    (Φ : Val rT → IProp GF) :
    ⊢ P s -∗ ↯ (∫⁻ x, F x ∂D.posterior s) -∗
      (∀ (t : S) (I : RationalInterval), ⌜D.refines s t ∧ D.Encloses t n I⌝ -∗
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
  rcases hI with ⟨rfl, hrefines, hencloses⟩
  isimp only [ViewOwns] at Hstate
  icases Hstate with ⟨_, Hstate⟩
  iapply Hcont $$ %t %I %⟨hrefines, hencloses⟩ Hstate Hcredit

end IsViewSpec

/-- A fixed ordinary oracle is itself a view; its ownership is retained once. -/
theorem IsOracleSpec.viewSpec (E : CoPset) (D : Model Ω S)
    (owns : Val rT → S → IProp GF) (h : IsOracleSpec E D owns) (handle : Val rT) :
    IsViewSpec E D (owns handle) handle where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨%hv, Hstate⟩
    subst v
    iapply h.wp handle s n F hF _ $$ Hstate Hcredit
    iintro %t %I %hI Hstate Hcredit
    iexists t, I
    isplit
    · ipureintro
      exact ⟨rfl, hI⟩
    isplitl [Hstate]
    · isimp only [ViewOwns]
      iframe Hstate
    iexact Hcredit

end specification

end

end SampLib.LatentReal
