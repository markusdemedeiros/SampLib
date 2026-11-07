import SampLib.Weighted.Support.TwoLevelChoice
import SampLib.Core.SupportedSpec

/-! # Categorical sampling through consecutive blocks

The program groups weights, chooses a block by its total, then chooses within
that block. Only positive-mass blocks reach the second categorical call.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.TwoLevelChoice

noncomputable section

private theorem positive_test (size : ℕ) (hs : 0 < size) :
    decide ((size : ℤ) ≤ 0) = false := decide_eq_false (by omega)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

variable [ProbLangDist.IsUniformInt rT]

/-- Conditional block sampling realizes the canonical categorical law for every positive size. -/
theorem twoLevelChoice_distSpec (E : CoPset) (ws : List ℕ) (size : ℕ)
    [NeZero ws.sum] [NeZero size] :
    IsDistSpec (GF := GF) E pl(&Occil.WeightedVariants.twoLevelChoice
      &(listVal (fun n : ℕ => Val.int n) ws).fst #int (size : ℤ) #())
      (WeightedChoice.law ws) (fun i : ℕ => Val.int (i : ℤ)) := by
  let : NeZero (WeightedBlocks.totals (WeightedBlocks.chunks size ws)).sum := ⟨by
    rw [WeightedBlocks.sum_totals]
    exact NeZero.ne ws.sum⟩
  refine ⟨fun F _ => ?_⟩
  iintro Hcredit
  twp_pures
  rw [positive_test size (NeZero.pos size)]
  twp_pure
  simp only [ClosedExp.openRec, ClosedExp.closeRec]
  twp_bind pl(&Occil.Weighted.validWeights &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedValidation.twp_validWeights E ws (NeZero.pos ws.sum)
  iintro %v %hv
  subst v
  iterate 2 twp_pure
  simp only [ClosedExp.openRec]
  twp_bind pl(&(groupTerm size) &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_group E size ws
  iintro %v %hv
  subst v
  iterate 2 twp_pure
  simp only [ClosedExp.openRec]
  twp_bind pl(&totalsTerm &(listVal (listVal (fun n : ℕ => Val.int n))
    (WeightedBlocks.chunks size ws)).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_totals E (WeightedBlocks.chunks size ws)
  iintro %v %hv
  subst v
  simp only [Exp.ofVal]
  twp_bind pl(&Occil.weightedChoice &(listVal (fun n : ℕ => Val.int n)
    (WeightedBlocks.totals (WeightedBlocks.chunks size ws))).fst)
  isimp only [← WeightedBlocks.expectation size ws F] at Hcredit
  iapply ((WeightedChoice.weightedChoice_distSpec E
    (WeightedBlocks.totals (WeightedBlocks.chunks size ws))).wp_supported
    (fun i => 0 < (WeightedBlocks.blockAt (WeightedBlocks.chunks size ws) i).sum)
    (Set.to_countable _).measurableSet (WeightedBlocks.ae_pos_block _)
    (WeightedBlocks.continuation size (WeightedBlocks.chunks size ws) F)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %i %hi Hcredit
  let : NeZero (WeightedBlocks.blockAt (WeightedBlocks.chunks size ws) i).sum := ⟨hi.ne'⟩
  twp_pure
  simp only [ClosedExp.openRec]
  twp_bind pl(&Occil.getAt &(listVal (listVal (fun n : ℕ => Val.int n))
    (WeightedBlocks.chunks size ws)).fst #int (i : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_blockAt E (WeightedBlocks.chunks size ws) i hi
  iintro %v %hv
  subst v
  simp only [Exp.ofVal]
  twp_bind pl(&Occil.weightedChoice &(listVal (fun n : ℕ => Val.int n)
    (WeightedBlocks.blockAt (WeightedBlocks.chunks size ws) i)).fst)
  isimp only [WeightedBlocks.continuation] at Hcredit
  iapply ((WeightedChoice.weightedChoice_distSpec E
    (WeightedBlocks.blockAt (WeightedBlocks.chunks size ws) i)).wp
    (fun j => F (i * size + j)) (measurable_of_countable _) _) $$ Hcredit
  iintro %j Hcredit
  twp_pures
  twp_value
  imodintro
  iexists i * size + j
  iframe Hcredit
  ipureintro
  exact Val.ext (by simp only [Nat.cast_add, Nat.cast_mul])

end specification

end

end SampLib.TwoLevelChoice
