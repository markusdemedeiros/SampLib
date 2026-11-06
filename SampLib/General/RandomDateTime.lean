import SampLib.Uniform.RndIntRange
import SampLib.Core.SamplerTerms
import Samplers.General.Core

/-! # Uniform integer timestamps

The timestamp wrapper inherits the inclusive integer-interval law.
-/

open ProbLang Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

namespace SampLib.RandomDateTime

noncomputable section

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Uniform timestamps over every nonempty inclusive interval. -/
theorem randomDateTime_distSpec (E : CoPset) (lo hi : ℤ) (h : lo ≤ hi) :
    IsDistSpec (GF := GF) E pl(&Occil.General.randomDateTime #int lo #int hi)
      (RndIntRange.law lo hi) Val.int where
  spec F hF := by
    iintro Hcredit
    iterate 2 twp_pure
    simp only [SamplerTerms.rndIntRange_openRec, SamplerTerms.rndIntRange_closeRec]
    iapply (RndIntRange.rndIntRange_distSpec E lo hi h).spec F hF $$ Hcredit

end

end SampLib.RandomDateTime
