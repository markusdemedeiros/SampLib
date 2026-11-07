import SampLib.PSRN.Support.Gamma.IntegerCore
import SampLib.PSRN.PSRNExponentialRational

/-! # The original positive-integer gamma constructor

A positive integer shape is a finite sum of independent exponential oracles.
The returned handle owns every component and retains arbitrary joint credits.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNGammaInteger

noncomputable section

open LatentReal

abbrev rate (a b : ℤ) : ℝ := (a : ℝ) / b
abbrev depth (shape : ℤ) : ℕ := shape.toNat - 1

def model (shape a b : ℤ) (ha : 0 < a) (hb : 0 < b) :=
  LatentGammaInteger.model
    (LatentExponential.model (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb)) (depth shape)

def initial (shape a b : ℤ) :=
  LatentGammaInteger.initial (LatentExponential.initial (rate a b)) (depth shape)

theorem index_shape (shape : ℤ) (hshape : 0 < shape) :
    ((depth shape + 1 : ℕ) : ℤ) = shape := by unfold depth; omega

theorem index_shape_real (shape : ℤ) (hshape : 0 < shape) :
    ((depth shape + 1 : ℕ) : ℝ) = (shape : ℝ) := by exact_mod_cast index_shape shape hshape

/-- Every valid source shape has exactly its canonical gamma law. -/
theorem model_law (shape a b : ℤ) (hshape : 0 < shape) (ha : 0 < a) (hb : 0 < b) :
    (model shape a b ha hb).law (initial shape a b) =
      ProbabilityTheory.gammaMeasure (shape : ℝ) (rate a b) := by
  have h := LatentGammaInteger.model_law
    (LatentExponential.model (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb))
    (LatentExponential.initial (rate a b)) (rate a b)
    (PSRNRationalRateDecay.rate_pos a b ha hb)
    (LatentExponential.initial_law (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb))
    (depth shape)
  simpa only [model, initial, index_shape_real shape hshape] using h

theorem measurable_error (shape a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    (model shape a b ha hb).MeasurableError :=
  LatentGammaInteger.measurable_error _
    (LatentExponential.measurable_error (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb)) _

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

abbrev exponentialOwns (a b : ℤ) : Val rT → LatentExponential.State (rate a b) → IProp GF :=
  PSRNExponential.owns (rate a b) (PSRNRationalRateDecay.value a b)

abbrev owns (shape a b : ℤ) := Core.owns (exponentialOwns (rT := rT) (GF := GF) a b) (depth shape)

/-- Full positive shape/rational-rate source specification, with owned observations. -/
theorem newGammaInteger_latentDistSpec (E : CoPset) (shape a b : ℤ)
    (hshape : 0 < shape) (ha : 0 < a) (hb : 0 < b) :
    IsLatentDistSpec (GF := GF) E pl(&Occil.PSRN.newGammaInteger #shape #a #b)
      (model shape a b ha hb) (initial shape a b) (owns shape a b) := by
  have h := Core.integer_latentDistSpec (rT := rT) (GF := GF) E a b
    (LatentExponential.model (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb))
    (LatentExponential.initial (rate a b)) (exponentialOwns (rT := rT) (GF := GF) a b)
    (PSRNExponential.newExponential_latentDistSpec (rT := rT) (GF := GF) E a b ha hb) (depth shape)
  simpa only [model, initial, owns, index_shape shape hshape] using h

end specification

end

end SampLib.PSRNGammaInteger
