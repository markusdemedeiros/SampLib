import SampLib.Samplers.PSRNGammaInteger
import SampLib.PSRNGammaIntegerRepresentedCore
import SampLib.LatentRepresentedExponentialWrappers

/-! # The integer-gamma oracle's actual deterministic interval schedule -/

open ProbLang

namespace SampLib.PSRNGammaInteger

noncomputable section

open LatentReal

def representation (shape a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    Representation (model shape a b ha hb) :=
  Represented.representation
    (LatentExponential.model (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb))
    (LatentExponential.representation (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb))
    (depth shape)

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The concrete positive-shape source certifies every sum interval and its whole joint credit. -/
theorem newGammaInteger_representedDistSpec (E : CoPset) (shape a b : ℤ)
    (hshape : 0 < shape) (ha : 0 < a) (hb : 0 < b) :
    IsRepresentedDistSpec (GF := GF) E pl(&Occil.PSRN.newGammaInteger #shape #a #b)
      (model shape a b ha hb) (representation shape a b ha hb) (initial shape a b)
      (owns shape a b) := by
  have h := Represented.integer_representedDistSpec (rT := rT) (GF := GF) E a b
    (LatentExponential.model (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb))
    (LatentExponential.representation (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb))
    (LatentExponential.initial (rate a b)) (exponentialOwns (rT := rT) (GF := GF) a b)
    (PSRNExponential.newExponential_representedDistSpec (rT := rT) (GF := GF) E a b ha hb)
    (depth shape)
  simpa only [model, initial, owns, representation, index_shape shape hshape] using h

end

end SampLib.PSRNGammaInteger
