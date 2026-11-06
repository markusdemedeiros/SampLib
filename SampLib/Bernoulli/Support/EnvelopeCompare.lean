import SampLib.Bernoulli.Support.EnvelopePosterior
import SampLib.Bernoulli.Support.UniformBagFractionChoice
import SampLib.Bernoulli.Syntax.EnvelopeFactory

/-! # The two owned-uniform comparisons of an envelope round -/

open ProbLang
open scoped ENNReal

namespace SampLib.EnvelopeFactory

open FactoryFractions

noncomputable section

private theorem afterRescale_as_choices {rT : Type} (self : Val rT) (l : Loc)
    (degree heads : ℕ) (lo hi : Fraction) :
    Program.afterRescale self l degree heads lo hi =
      UniformBag.fractionChoice l lo pl(#true)
        (UniformBag.fractionChoice l hi
          pl(&self.fst #int (degree : ℤ) #int (heads : ℤ) &lo.encode.fst &hi.encode.fst)
          pl(#false)) := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Returning uses the observed threshold; retrying retains both facts about the same uniform. -/
theorem twp_compare (E : CoPset) (a : Coefficients) (p : unitInterval)
    (F : Bool → ℝ≥0∞) (N t : ℕ) (x : a.State t) (self : Val rT) (l : Loc)
    (lo hi : Fraction)
    (hlo : (lo.value : ℝ) = (a.process p).lower t x)
    (hhi : (hi.value : ℝ) = (a.process p).upper t x)
    (hcontinue : ∀ q : List Bool,
      DyadicPosterior.resolves q ((a.process p).lower t x) false →
      DyadicPosterior.resolves q ((a.process p).upper t x) true →
      iprop(UniformBag.owns l q ∗ ↯ (a.credit p F N t x q)) ⊢
        tglWp E pl(&self.fst #int (a.degree t : ℤ) #int ((x.1 : ℕ) : ℤ)
          &lo.encode.fst &hi.encode.fst)
          (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))))
    (q : List Bool) :
    iprop(UniformBag.owns l q ∗ ↯ (a.credit p F N t x q)) ⊢
      tglWp E (Program.afterRescale self l (a.degree t) x.1 lo hi)
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  rw [afterRescale_as_choices]
  iintro ⟨Hbag, Hcredit⟩
  iapply UniformBag.twp_fractionChoice E l lo q ((a.process p).horizonCredit F N t x)
    ((a.process p).measurable_horizonCredit F N t x) pl(#true) _ _ ?_ ?_
  · intro r _ hlow
    iintro ⟨Hbag, Hcredit⟩
    twp_value
    imodintro
    iexists true
    ihave Hcredit := ErrorCredit.weaken
      (a.lower_credit p F N t x r (by simpa only [hlo] using hlow)) $$ Hcredit
    iframe Hcredit
    itrivial
  · intro r _ hlow
    iintro ⟨Hbag, Hcredit⟩
    iapply UniformBag.twp_fractionChoice E l hi r ((a.process p).horizonCredit F N t x)
      ((a.process p).measurable_horizonCredit F N t x) _ pl(#false) _ ?_ ?_
    · intro s hs hhigh
      iintro ⟨Hbag, Hcredit⟩
      have hlow' := DyadicPosterior.resolves_refines hs hlow
      iapply hcontinue s (by simpa only [hlo] using hlow')
        (by simpa only [hhi] using hhigh)
      iframe Hbag Hcredit
    · intro s _ hhigh
      iintro ⟨Hbag, Hcredit⟩
      twp_value
      imodintro
      iexists false
      ihave Hcredit := ErrorCredit.weaken
        (a.upper_credit p F N t x s (by simpa only [hhi] using hhigh)) $$ Hcredit
      iframe Hcredit
      itrivial
    · iframe Hbag Hcredit
  · iframe Hbag Hcredit

end specification

end

end SampLib.EnvelopeFactory
