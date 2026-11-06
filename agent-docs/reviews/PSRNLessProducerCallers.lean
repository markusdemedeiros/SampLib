import SampLib.PSRNLess

/-! Producer composition check: repeated comparisons retain one world and agree. -/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.Less.ProducerCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

private def twice (left right : Val rT) : Exp rT :=
  let call := .app (Program.acceptValue right).fst left.fst
  .app (.lam (.app (.lam (.pair (.bvar 1) (.bvar 0))) call)) call

private theorem measurable_second (Dleft Dright : Model Ω S)
    (H : Bool × Bool → Ω → ℝ≥0∞) (hH : ∀ p, Measurable (H p)) (b : Bool) :
    Measurable (fun x => H (b, decide (x ∈ event Dleft Dright)) x) := by
  change Measurable (outputCredit Dleft Dright (fun c x => H (b, c) x))
  exact measurable_outputCredit Dleft Dright (fun c x => H (b, c) x) (fun c => hH (b, c))

/-- Generic joint continuation credits and an unrelated resource survive two equal results. -/
theorem repeated (E : CoPset) (Dleft Dright : Model Ω S)
    (hworld : Dleft.SameWorld Dright) (hl : Dleft.MeasurableError) (hr : Dright.MeasurableError)
    (P : S → IProp GF) (left right : Val rT)
    (hleft : IsViewSpec E Dleft P left) (hright : IsViewSpec E Dright P right)
    (s : S) (H : Bool × Bool → Ω → ℝ≥0∞) (hH : ∀ p, Measurable (H p)) (R : IProp GF) :
    iprop(ViewOwns left (distinctState Dleft Dright P) left s ∗
      ↯ (∫⁻ x, H (decide (x ∈ event Dleft Dright), decide (x ∈ event Dleft Dright)) x
        ∂Dleft.posterior s) ∗ R) ⊢
      tglWp E (twice left right)
        (fun result : Val rT => iprop(∃ (b : Bool) (t : S),
          ⌜result = Val.pair (Val.bool b) (Val.bool b) ∧ Dleft.refines s t⌝ ∗
          ViewOwns left (distinctState Dleft Dright P) left t ∗
          ↯ (∫⁻ x, H (b, b) x ∂Dleft.posterior t) ∗ R)) := by
  iintro ⟨Hstate, Hcredit, HR⟩
  have hspec := less_eventSpec E Dleft Dright hworld hl hr P left right hleft hright
  twp_bind pl(&(Program.acceptValue right).fst &left.fst)
  iapply hspec.wp left s (fun b x => H (b, decide (x ∈ event Dleft Dright)) x)
    (measurable_second Dleft Dright H hH) _ $$ Hstate Hcredit
  iintro %a %t %ht Hstate Hcredit
  twp_pure
  twp_bind pl(&(Program.acceptValue right).fst &left.fst)
  iapply hspec.wp left t (fun b x => H (a, b) x) (fun b => hH (a, b)) _ $$ Hstate Hcredit
  iintro %b %u %hu Hstate Hcredit
  have hfirst : ∀ᵐ x ∂Dleft.posterior u,
      decide (x ∈ event Dleft Dright) = a :=
    (Dleft.absolutelyContinuous hu.1).ae_le ht.2
  have heq : a = b := by
    obtain ⟨x, hx, hy⟩ := (hfirst.and hu.2).exists
    exact hx.symm.trans hy
  subst b
  twp_pures
  twp_value
  imodintro
  iexists a, u
  iframe Hstate Hcredit HR
  ipureintro
  exact ⟨rfl, Dleft.refines_trans ht.1 hu.1⟩

#print axioms repeated

end

end SampLib.LatentReal.Less.ProducerCallers
