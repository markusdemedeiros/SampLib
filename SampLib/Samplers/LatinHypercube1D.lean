import SampLib.Syntax.Shuffle
import SampLib.Syntax.Stratified

/-! # Shuffled one-dimensional stratification

The bins use rounded integer boundaries. Their equal selection weights need not
give a uniform marginal on the whole grid when the bin widths differ.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatinHypercube1D

noncomputable section

section mathematics

open MeasureTheory

/-- Independent stratum jitter followed by an independent uniform position permutation. -/
def law (scale strata : ℕ) (hs : 0 < strata) (h : strata ≤ scale) : Measure (List ℤ) :=
  (Stratified1D.law scale strata hs h).bind
    (fun xs => (Shuffle.law xs).map (Shuffle.output xs))

instance (scale strata : ℕ) (hs : 0 < strata) (h : strata ≤ scale) :
    IsProbabilityMeasure (law scale strata hs h) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
    simp

/-- Conditioning on the jittered points leaves the uniform permutation expectation. -/
theorem expectation (scale strata : ℕ) (hs : 0 < strata) (h : strata ≤ scale)
    (F : List ℤ → ℝ≥0∞) :
    ∫⁻ xs, ∫⁻ σ, F (Shuffle.output xs σ) ∂Shuffle.law xs
        ∂Stratified1D.law scale strata hs h = ∫⁻ ys, F ys ∂law scale strata hs h := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable F).aemeasurable]
  apply lintegral_congr
  intro xs
  rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

end mathematics

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
