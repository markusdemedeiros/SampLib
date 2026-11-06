import SampLib.Weighted.Support.FastLoadedDiceRoot
import SampLib.Weighted.Support.KnuthYaoCertain
import SampLib.Common.WeightedValidation

/-! # The fast loaded dice roller for exact integer weights

The source traverses its padded dyadic matrix directly. Its implicit extra row
restarts the same walk; removing that rejection mass gives the original weights.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.FastLoadedDice

noncomputable section

open Program Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec ListValues.listVal_openRec

/-- The full original sampler has categorical probabilities `weight/total`, including zero rows. -/
theorem fastLoadedDiceRoller_distSpec (E : CoPset) (ws : List ℕ) [NeZero ws.sum] :
    IsDistSpec (GF := GF) E
      pl(&Occil.Weighted.fastLoadedDiceRoller &(listVal (fun w : ℕ => Val.int w) ws).fst #())
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
    twp_bind pl(&Occil.Weighted.powerOfTwoCeiling #int (ws.sum : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply PowerOfTwoCeiling.twp_powerOfTwoCeiling E ws.sum hT
    iintro %v %hv
    subst v
    twp_pure
    ieval (change _ ⊢ tglWp E (afterPadding ws (PowerOfTwoCeiling.width ws.sum) ws.sum) _)
    twp_pure
    twp_bind pl(&(KnuthYao.Program.find ws.sum)
      &(listVal (fun w : ℕ => Val.int w) ws).fst #0)
    iapply tglWp_wand
    isplitl []
    · iapply KnuthYao.twp_find E ws ws.sum 0
    iintro %v %hv
    subst v
    twp_pure
    cases hc : KnuthYao.certain ws ws.sum with
    | none =>
      simp only [KnuthYao.certainInt]
      iterate 4 twp_pure
      rw [show (PowerOfTwoCeiling.width ws.sum : ℤ) / 2 =
        ((PowerOfTwoCeiling.width ws.sum / 2 : ℕ) : ℤ) by omega]
      simp only [Exp.ofVal]
      ieval (
        change _ ⊢ tglWp E
          (run ws (2 ^ Nat.clog 2 ws.sum) (2 ^ Nat.clog 2 ws.sum / 2) 0) (resultPost F))
      isimp only [WeightedChoice.lintegral_law] at Hcredit
      have hloop := twp_loop (rT := rT) (GF := GF) E ws (Nat.clog 2 ws.sum) hT
        (PowerOfTwoCeiling.le_width ws.sum) (PowerOfTwoCeiling.width_le_double ws.sum hT)
        (KnuthYao.proper_of_none ws hc) F
      simp only [FastLoadedDiceCredits.credit] at hloop
      iapply hloop $$ Hcredit
    | some i =>
      simp only [KnuthYao.certainInt, Nat.zero_add]
      twp_pures
      twp_value
      imodintro
      iexists i
      isimp only [KnuthYao.certain_expectation ws hT i hc F] at Hcredit
      iframe Hcredit
      itrivial

end

end SampLib.FastLoadedDice
