import SampLib.PSRN.Support.PSRNExponential
import SampLib.PSRN.Support.PSRNExponentialCallbacks
import SampLib.PSRN.Support.PSRNExponentialWrapperSource

/-! # Logarithmic-rate exponential PSRNs -/

open ProbLang

namespace SampLib.PSRNExponential

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

abbrev logRateOwns (x y : ℤ) :
    Val rT → LatentExponential.State (PSRNLogRateDecay.rate x y) → IProp GF :=
  owns (PSRNLogRateDecay.rate x y) (PSRNLogRateDecay.value x y)

/-- Positive x>y gives rate log(x/y), using rational-power trials throughout. -/
theorem newExponentialLogRate_latentDistSpec (E : CoPset) (x y : ℤ)
    (hy : 0 < y) (hxy : y < x) :
    LatentReal.IsLatentDistSpec (GF := GF) E pl(&Occil.PSRN.newExponentialLogRate #x #y #())
      (LatentExponential.model (PSRNLogRateDecay.rate x y) (PSRNLogRateDecay.rate_pos hy hxy))
      (LatentExponential.initial (PSRNLogRateDecay.rate x y)) (logRateOwns x y) := by
  have hbase := newExponentialFromDecay_latentDistSpec (rT := rT) (GF := GF) E
    (PSRNLogRateDecay.rate x y) (PSRNLogRateDecay.rate_pos hy hxy)
    (PSRNLogRateDecay.value x y) (logRate_isDecaySpec E x y hy hxy)
  refine ⟨hbase.oracle, ?_⟩
  intro F hF
  iintro Hcredit
  iapply Wrappers.twp_log_open E x y _
  unfold Wrappers.logBody
  twp_pures
  have hguard : (decide (y ≤ 0) || decide (x ≤ y)) = false := by
    simp [not_le.mpr hy, not_le.mpr hxy]
  rw [hguard]
  twp_pure
  iapply hbase.spec F hF $$ Hcredit

end

end SampLib.PSRNExponential
