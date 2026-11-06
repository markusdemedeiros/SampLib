import SampLib.PSRN.Support.PSRNLindleyCore
import SampLib.PSRN.PSRNGammaInteger

/-! # The original Lindley sampler at every positive rational rate -/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNLindley

noncomputable section

open LatentReal

section mathematics

open MeasureTheory

abbrev rate := PSRNGammaInteger.rate

def model (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :=
  PSRNGammaMixture.Core.model
    (PSRNGammaMixtures.lindleyWeight (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb))
    (LatentExponential.model (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb))
    (LatentExponential.initial (rate a b)) 0 1

/-- The represented output is the standard shape-one/shape-two gamma mixture. -/
theorem model_law (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    (model a b ha hb).law .initial = PSRNGammaMixtures.law
      (PSRNGammaMixtures.lindleyWeight (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb))
      1 2 (rate a b) := by
  have h := PSRNGammaMixture.Core.model_law
    (PSRNGammaMixtures.lindleyWeight (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb))
    (LatentExponential.model (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb))
    (LatentExponential.initial (rate a b)) (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb)
    (LatentExponential.initial_law (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb)) 0 1
  simpa only [model, Nat.zero_add, Nat.cast_one, Nat.reduceAdd, Nat.cast_ofNat] using h

/-- In particular, the latent law has Lindley's familiar canonical density. -/
theorem model_law_density (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    (model a b ha hb).law .initial = volume.withDensity
      (fun x => ENNReal.ofReal (PSRNGammaMixtures.lindleyPDFReal (rate a b) x)) := by
  rw [model_law, PSRNGammaMixtures.lindley_law_eq_withDensity
    (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb)]

theorem measurable_error (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    (model a b ha hb).MeasurableError :=
  PSRNGammaMixture.Core.measurable_error _ _ _
    (LatentExponential.measurable_error (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb)) 0 1

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

abbrev owns (a b : ℤ) :=
  PSRNGammaMixture.Core.owns (PSRNGammaInteger.exponentialOwns (rT := rT) (GF := GF) a b) 0 1

/-- The actual Lindley program retains its selected oracle and arbitrary joint credit. -/
theorem newLindley_latentDistSpec (E : CoPset) (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    IsLatentDistSpec (GF := GF) E pl(&Occil.PSRN.newLindley #a #b #())
      (model a b ha hb) .initial (owns a b) := by
  have h := Core.lindley_latentDistSpec (rT := rT) (GF := GF)
    E a b ha hb
    (LatentExponential.model (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb))
    (LatentExponential.initial (rate a b))
    (PSRNGammaInteger.exponentialOwns (rT := rT) (GF := GF) a b)
    (PSRNExponential.newExponential_latentDistSpec (rT := rT) (GF := GF) E a b ha hb)
  simpa only [model, owns, Core.rate, PSRNGammaInteger.rate] using h

end specification

end

end SampLib.PSRNLindley
