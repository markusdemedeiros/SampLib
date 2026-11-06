import SampLib.PSRN.PSRNExponentialRational
import SampLib.PSRN.PSRNExponentialLogRate
import SampLib.PSRN.PSRNExponentialUnknownRate

/-! # Deterministic interval certificates for the concrete exponential interfaces -/

open ProbLang Iris TotalEris

namespace SampLib.PSRNExponential

noncomputable section

section integer

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]

theorem newExponential_representedDistSpec (E : CoPset) (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    LatentReal.IsRepresentedDistSpec (GF := GF) E pl(&Occil.PSRN.newExponential #a #b #())
      (LatentExponential.model ((a : ℝ) / b) (PSRNRationalRateDecay.rate_pos a b ha hb))
      (LatentExponential.representation ((a : ℝ) / b) (PSRNRationalRateDecay.rate_pos a b ha hb))
      (LatentExponential.initial ((a : ℝ) / b)) (rationalOwns a b) where
  toIsLatentPayloadSpec :=
    (newExponential_latentDistSpec (rT := rT) (GF := GF) E a b ha hb).payloadSpec
  oracle := (newExponentialFromDecay_representedDistSpec (rT := rT) (GF := GF) E
    ((a : ℝ) / b) (PSRNRationalRateDecay.rate_pos a b ha hb) (PSRNRationalRateDecay.value a b)
    (rational_isDecaySpec E a b ha hb)).oracle

theorem newExponentialLogRate_representedDistSpec (E : CoPset) (x y : ℤ)
    (hy : 0 < y) (hxy : y < x) :
    LatentReal.IsRepresentedDistSpec (GF := GF) E pl(&Occil.PSRN.newExponentialLogRate #x #y #())
      (LatentExponential.model (PSRNLogRateDecay.rate x y) (PSRNLogRateDecay.rate_pos hy hxy))
      (LatentExponential.representation (PSRNLogRateDecay.rate x y)
        (PSRNLogRateDecay.rate_pos hy hxy))
      (LatentExponential.initial (PSRNLogRateDecay.rate x y)) (logRateOwns x y) where
  toIsLatentPayloadSpec :=
    (newExponentialLogRate_latentDistSpec (rT := rT) (GF := GF) E x y hy hxy).payloadSpec
  oracle := (newExponentialFromDecay_representedDistSpec (rT := rT) (GF := GF) E
    (PSRNLogRateDecay.rate x y) (PSRNLogRateDecay.rate_pos hy hxy) (PSRNLogRateDecay.value x y)
    (logRate_isDecaySpec E x y hy hxy)).oracle

end integer

section unknown

variable [ProbLangDist ℝ] [ProbLangDist.IsUniformInt ℝ] [ProbLangDist.IsUniformReal ℝ]
  [ProbLangFFI ℝ] [ProbLangObs ℝ]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]

theorem newExponentialUnknownRate_representedDistSpec (E : CoPset) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (coin : Val ℝ)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    LatentReal.IsRepresentedDistSpec (GF := GF) E
      pl(&Occil.PSRN.newExponentialUnknownRate &coin.fst #())
      (LatentExponential.model (p : ℝ) hp) (LatentExponential.representation (p : ℝ) hp)
      (LatentExponential.initial (p : ℝ)) (unknownRateOwns p coin) where
  toIsLatentPayloadSpec :=
    (newExponentialUnknownRate_latentDistSpec (GF := GF) E p hp coin hcoin).payloadSpec
  oracle := (newExponentialFromDecay_representedDistSpec (GF := GF) E (p : ℝ) hp
    (PSRNUnknownRateDecay.value coin) (unknownRate_isDecaySpec E p hp coin hcoin)).oracle

end unknown

end

end SampLib.PSRNExponential
