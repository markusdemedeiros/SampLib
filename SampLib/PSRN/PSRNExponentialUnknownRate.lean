import SampLib.PSRN.Support.PSRNExponential
import SampLib.PSRN.Support.PSRNExponentialCallbacks
import SampLib.PSRN.Support.PSRNExponentialWrapperSource

/-! # Exponential PSRNs at an unknown positive coin bias -/

open ProbLang

namespace SampLib.PSRNExponential

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformInt ℝ] [ProbLangDist.IsUniformReal ℝ]
  [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

abbrev unknownRateOwns (p : unitInterval) (coin : Val ℝ) :
    Val ℝ → LatentExponential.State (p : ℝ) → IProp GF :=
  owns (p : ℝ) (PSRNUnknownRateDecay.value coin)

/-- Every positive unknown bias, including one, gives an owned exponential draw. -/
theorem newExponentialUnknownRate_latentDistSpec (E : CoPset) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (coin : Val ℝ)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    LatentReal.IsLatentDistSpec (GF := GF) E
      pl(&Occil.PSRN.newExponentialUnknownRate &coin.fst #())
      (LatentExponential.model (p : ℝ) hp) (LatentExponential.initial (p : ℝ))
      (unknownRateOwns p coin) := by
  have hbase := newExponentialFromDecay_latentDistSpec (GF := GF) E (p : ℝ) hp
    (PSRNUnknownRateDecay.value coin) (unknownRate_isDecaySpec E p hp coin hcoin)
  refine ⟨hbase.oracle, ?_⟩
  intro F hF
  iintro Hcredit
  iapply Wrappers.twp_unknown_open E coin _
  unfold Wrappers.unknownBody
  iapply hbase.spec F hF $$ Hcredit

end

end SampLib.PSRNExponential
