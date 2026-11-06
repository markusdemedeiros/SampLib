import SampLib.Core.Laws.FiniteGrid
import SampLib.Core.SupportedSpec
import SampLib.Core.Syntax.UniformRanges

/-! # Reuse uniform integer proposals with finite latent positions -/

open ProbLang
open scoped ENNReal

namespace SampLib.FiniteGrid

noncomputable section

def proposal {rT : Type _} (lower : ℤ) (width : ℕ) : Val rT :=
  ⟨pl(fun u, &Occil.rndIntExcRange #lower #int (lower + (width : ℤ))),
    .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] RndIntExcRange.rndIntExcRange_openRec
  RndIntExcRange.rndIntExcRange_closeRec

/-- Transport the verified interval sampler, using its almost-sure support. -/
theorem range_distSpec (E : CoPset) (lower : ℤ) (width : ℕ) [NeZero width] :
    IsDistSpec (GF := GF) E pl(&Occil.rndIntExcRange #lower #int (lower + (width : ℤ)))
      (law width) (fun i => Val.int (point lower i)) where
  spec F _ := by
    iintro Hcredit
    isimp only [← range_expectation lower width F] at Hcredit
    iapply ((RndIntExcRange.rndIntExcRange_distSpec E lower (lower + (width : ℤ))
      (lower_lt_upper lower width)).wp_supported
      (fun z => z ∈ Set.Ico lower (lower + (width : ℤ))) measurableSet_Ico
      (RndIntExcRange.ae_mem lower (lower + (width : ℤ)) (lower_lt_upper lower width))
      (fun z => F (position lower width z)) (measurable_of_countable _) _) $$ Hcredit
    iintro %z %hz Hcredit
    iexists position lower width z
    iframe Hcredit
    ipureintro
    exact congrArg Val.int (point_position lower width z hz).symm

/-- The unit callback expected by rejection sampling. -/
theorem proposal_distSpec (E : CoPset) (lower : ℤ) (width : ℕ) [NeZero width] :
    IsDistSpec (GF := GF) E pl(&(proposal lower width).fst #())
      (law width) (fun i => Val.int (point lower i)) where
  spec F hF := by
    iintro Hcredit
    twp_pure
    iapply ((range_distSpec E lower width).wp F hF _) $$ Hcredit
    iintro %i Hcredit
    iexists i
    iframe Hcredit
    itrivial

end specification

end

end SampLib.FiniteGrid
