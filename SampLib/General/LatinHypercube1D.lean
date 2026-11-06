import SampLib.Common.Syntax.Shuffle
import SampLib.General.Syntax.Stratified
import SampLib.General.Laws.LatinHypercube1D

/-! # Shuffled one-dimensional stratification

The bins use rounded integer boundaries. Their equal selection weights need not
give a uniform marginal on the whole grid when the bin widths differ.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatinHypercube1D

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Uniformly reorder one independent grid draw from each stratum. -/
theorem latinHypercube1D_distSpec (E : CoPset) (scale strata : ℕ)
    (hs : 0 < strata) (h : strata ≤ scale) :
    IsDistSpec (GF := GF) E
      pl(&Occil.General.latinHypercube1D #int (scale : ℤ) #int (strata : ℤ) #())
      (law scale strata hs h) (listVal Val.int) where
  spec F _ := by
    iintro Hcredit
    iterate 3 twp_pure
    simp only [Shuffle.shuffle_openRec, Shuffle.shuffle_closeRec,
      Stratified1D.stratified1D_openRec, Stratified1D.stratified1D_closeRec]
    twp_bind pl(&Occil.General.stratified1D #int (scale : ℤ) #int (strata : ℤ) #())
    isimp only [← expectation scale strata hs h F] at Hcredit
    iapply ((Stratified1D.stratified1D_distSpec E scale strata hs h).wp
      (fun xs => ∫⁻ σ, F (Shuffle.output xs σ) ∂Shuffle.law xs)
      (measurable_of_countable _) _) $$ Hcredit
    iintro %xs Hcredit
    isimp only [Exp.ofVal]
    iapply ((Shuffle.shuffle_distSpec E Val.int xs).wp
      (fun σ => F (Shuffle.output xs σ)) (measurable_of_countable _) _) $$ Hcredit
    iintro %σ Hcredit
    iexists Shuffle.output xs σ
    iframe Hcredit
    itrivial

end specification

end

end SampLib.LatinHypercube1D
