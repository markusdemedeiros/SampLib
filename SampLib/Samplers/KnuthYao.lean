import SampLib.KnuthYaoLoop
import SampLib.KnuthYaoCertain
import SampLib.WeightedValidation

/-! # Knuth–Yao from exact nonnegative integer weights

The source first handles a certain row. Otherwise its actual rational columns
have fewer live ranks than categories, so the DDG cutoff residual vanishes.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.KnuthYao

noncomputable section

open Program Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec ListValues.listVal_openRec

/-- Each category has its exact integer weight divided by the positive total. -/
theorem knuthYao_distSpec (E : CoPset) (ws : List ℕ) [NeZero ws.sum] :
    IsDistSpec (GF := GF) E
      pl(&Occil.Weighted.knuthYao &(listVal (fun w : ℕ => Val.int w) ws).fst #())
      (WeightedChoice.law ws) (fun i => Val.int (i : ℤ)) where
  spec F _ := by
    have hT := NeZero.pos ws.sum
    iintro Hcredit
    rw [← source_fst (rT := rT)]
    iterate 2 twp_pure
    twp_bind pl(&Occil.Weighted.validWeights &(listVal (fun w : ℕ => Val.int w) ws).fst)
    iapply tglWp_wand
    isplitl []
    · iapply WeightedValidation.twp_validWeights E ws hT
    iintro %v %hv
    subst v
    twp_pure
    twp_bind pl(&Occil.sumInts &(listVal (fun w : ℕ => Val.int w) ws).fst)
    iapply tglWp_wand
    isplitl []
    · iapply WeightedChoice.twp_sumInts E ws
    iintro %v %hv
    subst v
    twp_pure
    ieval (change _ ⊢ tglWp E (afterTotal ws ws.sum) _)
    twp_pure
    twp_bind pl(&(find ws.sum) &(listVal (fun w : ℕ => Val.int w) ws).fst #0)
    iapply tglWp_wand
    isplitl []
    · iapply twp_find E ws ws.sum 0
    iintro %v %hv
    subst v
    twp_pure
    cases hc : certain ws ws.sum with
    | none =>
      simp only [certainInt]
      iterate 3 twp_pure
      have hloop := twp_loop (rT := rT) (GF := GF) E ws hT (proper_of_none ws hc) F
      simp only [loop_eq] at hloop
      iapply hloop $$ Hcredit
    | some i =>
      simp only [certainInt, Nat.zero_add]
      twp_pures
      twp_value
      imodintro
      iexists i
      isimp only [certain_expectation ws hT i hc F] at Hcredit
      iframe Hcredit
      itrivial

end

end SampLib.KnuthYao
