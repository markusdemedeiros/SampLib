import SampLib.PSRN.Support.Gamma.MixtureCore
import SampLib.PSRN.PSRNGammaInteger

/-! # The original mixture of two positive integer gamma oracles -/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNGammaMixture

noncomputable section

open LatentReal

abbrev rate := PSRNGammaInteger.rate

def model (p : unitInterval) (leftShape rightShape a b : ℤ) (ha : 0 < a) (hb : 0 < b) :=
  Core.model p
    (LatentExponential.model (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb))
    (LatentExponential.initial (rate a b))
    (PSRNGammaInteger.depth leftShape) (PSRNGammaInteger.depth rightShape)

/-- The selector weights the two canonical gamma laws, including either endpoint weight. -/
theorem model_law (p : unitInterval) (leftShape rightShape a b : ℤ)
    (hleft : 0 < leftShape) (hright : 0 < rightShape) (ha : 0 < a) (hb : 0 < b) :
    (model p leftShape rightShape a b ha hb).law .initial =
      PSRNGammaMixtures.law p (leftShape : ℝ) (rightShape : ℝ) (rate a b) := by
  have h := Core.model_law p
    (LatentExponential.model (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb))
    (LatentExponential.initial (rate a b)) (rate a b)
    (PSRNRationalRateDecay.rate_pos a b ha hb)
    (LatentExponential.initial_law (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb))
    (PSRNGammaInteger.depth leftShape) (PSRNGammaInteger.depth rightShape)
  simpa only [model, PSRNGammaInteger.index_shape_real leftShape hleft,
    PSRNGammaInteger.index_shape_real rightShape hright] using h

theorem measurable_error (p : unitInterval) (leftShape rightShape a b : ℤ)
    (ha : 0 < a) (hb : 0 < b) : (model p leftShape rightShape a b ha hb).MeasurableError :=
  Core.measurable_error _ _ _
    (LatentExponential.measurable_error (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb)) _ _

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

abbrev owns (leftShape rightShape a b : ℤ) :=
  Core.owns (PSRNGammaInteger.exponentialOwns (rT := rT) (GF := GF) a b)
    (PSRNGammaInteger.depth leftShape) (PSRNGammaInteger.depth rightShape)

/-- The complete rational-selector, positive-integer-shape, positive-rational-rate domain. -/
theorem newGammaMixture_latentDistSpec (E : CoPset) (wa wb : ℤ)
    (hwa : 0 ≤ wa) (hwb : 0 < wb) (hw : wa ≤ wb) (leftShape rightShape a b : ℤ)
    (hleft : 0 < leftShape) (hright : 0 < rightShape) (ha : 0 < a) (hb : 0 < b) :
    IsLatentDistSpec (GF := GF) E
      pl(&Occil.PSRN.newGammaMixture #wa #wb #leftShape #rightShape #a #b #())
      (model (RationalCoin.bias wa wb hwa hwb hw) leftShape rightShape a b ha hb)
      .initial (owns leftShape rightShape a b) := by
  have h := Core.mixture_latentDistSpec (rT := rT) (GF := GF)
    E wa wb hwa hwb hw a b
    (LatentExponential.model (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb))
    (LatentExponential.initial (rate a b))
    (PSRNGammaInteger.exponentialOwns (rT := rT) (GF := GF) a b)
    (PSRNExponential.newExponential_latentDistSpec (rT := rT) (GF := GF) E a b ha hb)
    (PSRNGammaInteger.depth leftShape) (PSRNGammaInteger.depth rightShape)
  simpa only [model, owns, PSRNGammaInteger.index_shape leftShape hleft,
    PSRNGammaInteger.index_shape rightShape hright] using h

end specification

end

end SampLib.PSRNGammaMixture
