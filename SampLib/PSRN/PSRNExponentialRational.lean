import SampLib.PSRN.Support.PSRNExponential
import SampLib.PSRN.Support.PSRNExponentialCallbacks
import SampLib.PSRN.Support.PSRNExponentialWrapperSource

/-! # Rational-rate exponential PSRNs -/

open ProbLang

namespace SampLib.PSRNExponential

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Ownership keeps the actual rational decay callback in the deferred fractional closure. -/
abbrev rationalOwns (a b : ℤ) : Val rT → LatentExponential.State ((a : ℝ) / b) → IProp GF :=
  owns ((a : ℝ) / b) (PSRNRationalRateDecay.value a b)

/-- Every positive rational rate gives an observable draw from the canonical exponential law. -/
theorem newExponential_latentDistSpec (E : CoPset) (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    LatentReal.IsLatentDistSpec (GF := GF) E pl(&Occil.PSRN.newExponential #a #b #())
      (LatentExponential.model ((a : ℝ) / b) (PSRNRationalRateDecay.rate_pos a b ha hb))
      (LatentExponential.initial ((a : ℝ) / b)) (rationalOwns a b) := by
  have hbase := newExponentialFromDecay_latentDistSpec (rT := rT) (GF := GF) E
    ((a : ℝ) / b) (PSRNRationalRateDecay.rate_pos a b ha hb)
    (PSRNRationalRateDecay.value a b) (rational_isDecaySpec E a b ha hb)
  refine ⟨hbase.oracle, ?_⟩
  intro F hF
  iintro Hcredit
  iapply Wrappers.twp_rational_open E a b _
  unfold Wrappers.rationalBody
  twp_pures
  have hguard : (decide (a ≤ 0) || decide (b ≤ 0)) = false := by
    simp [not_le.mpr ha, not_le.mpr hb]
  rw [hguard]
  twp_pure
  iapply hbase.spec F hF $$ Hcredit

end

end SampLib.PSRNExponential
