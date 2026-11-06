import SampLib.PSRN.Support.PSRNExponentialOracle
import SampLib.PSRN.Support.LatentExponentialSource

/-! # The decay-based exponential sampler

The whole-part counter samples a geometric strip. The fractional constructor
defers its conditional exponential digits, and rational translation joins the two
coordinates without observing the fractional tail.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNExponential

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Sample the whole strip, defer its fractional digits, then retain their joint credit. -/
theorem twp_newExponentialFromDecay (E : CoPset) (rate : ℝ) (hrate : 0 < rate)
    (decay : Val rT) (hdecay : IsDecaySpec (GF := GF) E rate hrate decay)
    (F : ℕ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    iprop(↯ (∫⁻ z, F z ∂(LatentExponential.model rate hrate).posterior
      (LatentExponential.initial rate))) ⊢
      tglWp E pl(&Occil.PSRN.newExponentialFromDecay &decay.fst #())
        (fun v : Val rT => iprop(∃ t : LatentExponential.State rate,
          ⌜(LatentExponential.model rate hrate).refines (LatentExponential.initial rate) t⌝ ∗
          owns rate decay v t ∗
          ↯ (∫⁻ z, F z ∂(LatentExponential.model rate hrate).posterior t))) := by
  have := ExponentialDigits.fraction_probability rate hrate
  let wholeCredit := fun k : ℕ => ∫⁻ x, F (k, x) ∂ExponentialDigits.fraction rate
  have hwhole := whole_distSpec (rT := rT) (GF := GF) E rate hrate decay hdecay
  have hdigits := LatentDigits.newByDigits_latentDistSpec (rT := rT) (GF := GF) E
    (ExponentialDigits.fraction rate) ExponentialDigits.digits ExponentialDigits.measurable_digits
    (ExponentialLogistic.Program.digitVal decay) (digitSpec E rate hrate decay hdecay)
  iintro Hcredit
  isimp only [LatentExponential.initial_expectation rate hrate F hF] at Hcredit
  iapply Program.twp_open E decay _
  iapply Program.twp_afterCount E decay _
  unfold Program.countBody
  twp_bind pl(&(ExponentialCount.Program.countVal decay).fst #0)
  iapply (hwhole.wp wholeCredit (measurable_of_countable _) _) $$ Hcredit
  iintro %k Hcredit
  ieval (change _ ⊢ tglWp E (.app (.lam (Program.afterWhole decay)) (.lit (.int (k : ℤ)))) _)
  iapply Program.twp_afterWhole E decay (k : ℤ) _
  unfold Program.wholeBody Program.digits
  twp_bind pl(&Occil.PSRN.newByDigits &(ExponentialLogistic.Program.digitVal decay).fst #())
  have hbudget :
      (∫⁻ x, F (k, x) ∂(LatentDigits.model (ExponentialDigits.fraction rate)
        ExponentialDigits.digits ExponentialDigits.measurable_digits).posterior
          (LatentDigits.initial (ExponentialDigits.fraction rate) ExponentialDigits.digits)) =
        wholeCredit k := by
    simp only [LatentDigits.posterior_initial, wholeCredit]
  isimp only [← hbudget] at Hcredit
  iapply (hdigits.wp (fun x => F (k, x))
    (hF.comp (measurable_const.prodMk measurable_id)) _) $$ Hcredit
  iintro %fraction %p %hrefines Hstate Hcredit
  isimp only [LatentDigits.model] at Hcredit
  ieval (change _ ⊢ tglWp E (.app (.lam (Program.afterDigits (k : ℤ))) fraction.fst) _)
  iapply Program.twp_afterDigits E (k : ℤ) fraction _
  iapply tglWp_wand
  isplitl [Hstate]
  · iapply LatentReal.twp_translate E (fractionOwns rate decay) fraction p (k : ℤ) 1 (by decide)
    iexact Hstate
  iintro %v Hstate
  iexists some (k, p)
  isplit
  · ipureintro
    exact LatentExponential.initial_refines rate hrate _
  isimp only [owns, LatentExponential.some_expectation rate hrate k p F hF]
  iframe Hstate Hcredit

/-- The original constructor retains the exact whole-plus-digits interval representation. -/
theorem newExponentialFromDecay_representedDistSpec (E : CoPset) (rate : ℝ) (hrate : 0 < rate)
    (decay : Val rT) (hdecay : IsDecaySpec (GF := GF) E rate hrate decay) :
    LatentReal.IsRepresentedDistSpec (GF := GF) E
      pl(&Occil.PSRN.newExponentialFromDecay &decay.fst #())
      (LatentExponential.model rate hrate) (LatentExponential.representation rate hrate)
      (LatentExponential.initial rate) (owns rate decay) where
  oracle := representedOracleSpec E rate hrate decay hdecay
  spec F hF := twp_newExponentialFromDecay E rate hrate decay hdecay F hF

/-- The owned latent law is available independently of its stronger interval certificate. -/
theorem newExponentialFromDecay_latentDistSpec (E : CoPset) (rate : ℝ) (hrate : 0 < rate)
    (decay : Val rT) (hdecay : IsDecaySpec (GF := GF) E rate hrate decay) :
    LatentReal.IsLatentDistSpec (GF := GF) E
      pl(&Occil.PSRN.newExponentialFromDecay &decay.fst #())
      (LatentExponential.model rate hrate) (LatentExponential.initial rate) (owns rate decay) :=
  (newExponentialFromDecay_representedDistSpec E rate hrate decay hdecay).forget

end

end SampLib.PSRNExponential
