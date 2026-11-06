import SampLib.Weighted.Support.OptimalMatrix
import SampLib.Weighted.Support.OptimalDraw
import SampLib.Weighted.Syntax.OptimalChoice
import SampLib.Weighted.Laws.OptimalSingleton

/-! # Finite cyclic weighted choice, including zero and certain weights -/

open ProbLang
open scoped ENNReal

namespace SampLib.Optimal

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open OptimalEncoding OptimalMatrix

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec ListValues.listVal_openRec
  WeightedValidation.validWeights_openRec WeightedValidation.validWeights_closeRec

private theorem length_test {rT : Type} [BEq rT] (n : ℕ) :
    ((BaseLit.int (n : ℤ) : BaseLit rT) == .int 1) = decide (n = 1) := by
  change decide ((n : ℤ) = ((1 : ℕ) : ℤ)) = decide (n = 1)
  simp only [Int.natCast_inj]

private theorem twp_createdDraw (E : CoPset) (ws : List ℕ) (hs : 0 < ws.sum)
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) -∗
      tglWp E pl(&Occil.WeightedVariants.optimalDraw
        &(Table.value (create ws) : Val rT).fst #()) (OptimalWalk.post F) := by
  have hp := OptimalParameters.selected_valid hs
  have hD : ws.sum ≤ denominator ws.sum.size (OptimalParameters.selected ws.sum).1 := by
    simpa only [hp.2.1] using hp.2.2
  have hupper : denominator ws.sum.size (OptimalParameters.selected ws.sum).1 ≤ 2 * ws.sum := by
    rw [← hp.2.1]
    exact selected_le_twice hs
  rw [create_eq_table ws hs]
  exact twp_optimalDraw E ws ws.sum.size (OptimalParameters.selected ws.sum).1
    hp.1 hs hD hupper F

/-- Direct traversal of the table generated for any positive-total nonnegative weight vector. -/
theorem optimalDraw_distSpec (E : CoPset) (ws : List ℕ) [NeZero ws.sum] :
    IsDistSpec (GF := GF) E pl(&Occil.WeightedVariants.optimalDraw
      &(Table.value (create ws) : Val rT).fst #())
      (WeightedChoice.law ws) (fun i => Val.int (i : ℤ)) where
  spec F _ := by
    have h := twp_createdDraw (rT := rT) (GF := GF) E ws
      (Nat.pos_of_ne_zero (NeZero.ne ws.sum)) F
    unfold OptimalWalk.post at h
    exact wand_entails h

private theorem twp_choice (E : CoPset) (ws : List ℕ) (hs : 0 < ws.sum)
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) -∗
      tglWp E pl(&Occil.WeightedVariants.optimalChoice &(listValNatInts ws).fst #())
        (OptimalWalk.post F) := by
  iintro Hcredit
  rw [Program.choice_source_eq (rT := rT)]
  iterate 2 twp_pure
  twp_bind pl(&Occil.Weighted.validWeights &(listValNatInts ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedValidation.twp_validWeights E ws hs
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.length &(listValNatInts ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_length E (fun n : ℕ => Val.int (n : ℤ)) ws
  iintro %v %hv
  subst v
  twp_pure
  rw [length_test (rT := rT)]
  by_cases hlen : ws.length = 1
  · rw [decide_eq_true hlen]
    twp_pure
    obtain ⟨w, rfl⟩ := List.length_eq_one_iff.mp hlen
    have hw : 0 < w := by simpa using hs
    isimp only [singleton_credit w hw F] at Hcredit
    twp_value
    imodintro
    isimp only [OptimalWalk.post]
    iexists 0
    iframe Hcredit
    itrivial
  · rw [decide_eq_false hlen]
    twp_pure
    twp_bind pl(&Occil.WeightedVariants.optimalMatrix &(listValNatInts ws).fst)
    iapply tglWp_wand
    isplitl []
    · iapply twp_optimalMatrix E ws hs
    iintro %v %hv
    subst v
    simp only [Exp.ofVal]
    iapply twp_createdDraw E ws hs F $$ Hcredit

/-- The original preprocessing wrapper samples each original label with weight/total mass. -/
theorem optimalChoice_distSpec (E : CoPset) (ws : List ℕ) [NeZero ws.sum] :
    IsDistSpec (GF := GF) E
      pl(&Occil.WeightedVariants.optimalChoice &(listValNatInts ws).fst #())
      (WeightedChoice.law ws) (fun i => Val.int (i : ℤ)) where
  spec F _ := by
    have h := twp_choice (rT := rT) (GF := GF) E ws
      (Nat.pos_of_ne_zero (NeZero.ne ws.sum)) F
    unfold OptimalWalk.post at h
    exact wand_entails h

end

end SampLib.Optimal
