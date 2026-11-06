import SampLib.PSRN.Support.LatentRepresentedDivision

open ProbLang
open scoped ENNReal

namespace RepresentedDivisionCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib.LatentReal

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

example (E : CoPset) (D : Model Ω S) (R : Representation D) (P : S → IProp GF)
    (source : Val rT) (h : IsRepresentedViewSpec E D R P source) :=
  RepresentedDivision.viewSpec E D D (.refl D) R R P source source h h

example (D : Model Ω S) (R : Representation D) (s : S)
    (hn : RepresentedReciprocalView.Nonzero D s) :
    ∀ᵐ x ∂D.posterior s, (RepresentedDivision.model D D (.refl D) R).value x = 1 := by
  filter_upwards [hn] with x hx
  rw [RepresentedDivision.value_eq, div_self hx]

example (E : CoPset) (D : Model Ω S) (P : S → IProp GF) (a b : Val rT) (s : S) :=
  RepresentedDivision.twp_constructor E D P a b s

theorem frame (E : CoPset) (D : Model Ω S) (R : Representation D) (P : S → IProp GF)
    (v : Val rT) (h : IsRepresentedViewSpec E D R P v) (s : S) (n : ℕ)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) (I : IProp GF) (Φ : Val rT → IProp GF) :
    ⊢ (P s ∗ I) -∗ ↯ (∫⁻ x, F x ∂D.posterior s) -∗
      (∀ (t : S) (J : RationalInterval),
        ⌜D.refines s t ∧ D.Encloses t n J ∧ R.Observed t n J⌝ -∗
        P t -∗ ↯ (∫⁻ x, F x ∂D.posterior t) -∗ I -∗ Φ (intervalVal J)) -∗
      tglWp E pl(&v.fst #int (n : ℤ)) Φ := by
  iintro ⟨Hstate, HI⟩ Hcredit Hcont
  iapply (IsRepresentedViewSpec.wp h s n F hF _) $$ Hstate Hcredit
  iintro %t %J %hJ Hstate Hcredit
  iapply Hcont $$ %t %J %hJ Hstate Hcredit HI

example (E : CoPset) (D : Model Ω S) (R : Representation D) (P : S → IProp GF)
    (source : Val rT) (h : IsRepresentedViewSpec E D R P source) (s : S) (n : ℕ)
    (I : IProp GF) (Φ : Val rT → IProp GF) :=
  frame E _ _ _ _ (RepresentedDivision.viewSpec E D D (.refl D) R R P source source h h)
    s n (fun _ => ∞) measurable_const I Φ

#print axioms represented_view_withInvariant
#print axioms RepresentedReciprocalView.owns_fixed
#print axioms RepresentedReciprocalView.viewSpec
#print axioms RepresentedDivision.Program.twp_open
#print axioms RepresentedDivision.twp_constructor
#print axioms RepresentedDivision.viewSpec

end

end RepresentedDivisionCallers
