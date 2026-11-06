import SampLib.Weighted.Support.SuccinctChoiceProposal

/-! # Exact categorical rejection with 20/32-bit packed weights -/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.SuccinctChoice

noncomputable section

/-- Dense vectors use direct rejection; the packed branch requires representable weights. -/
def Admissible (ws : List ℕ) : Prop :=
  2 ^ 19 * ws.length ≤ ws.sum ∨ ∀ w ∈ ws, w < 2 ^ 32

private theorem dense_test (ws : List ℕ) :
    decide ((524288 : ℤ) * ws.length ≤ ws.sum) = decide (2 ^ 19 * ws.length ≤ ws.sum) := by
  apply decide_eq_decide.mpr
  norm_num only [Nat.reducePow]
  norm_cast

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open scoped SampLib.SuccinctChoice.Program

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec Program.weights_closeRec
  WeightedValidation.validWeights_openRec
  WeightedValidation.validWeights_closeRec WeightedValidation.sumInts_openRec
  WeightedValidation.sumInts_closeRec GeneralSyntax.length_openRec GeneralSyntax.length_closeRec

/-- Both source branches implement the same exact categorical law. -/
theorem twp_succinctChoice (E : CoPset) (ws : List ℕ) (ht : 0 < ws.sum)
    (hwords : Admissible ws) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) -∗
      tglWp E pl(&Occil.WeightedVariants.succinctChoice
        &(listVal (fun n : ℕ => Val.int n) ws).fst #())
        (fun v => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ ↯ (F i))) := by
  let m := WeightMaximum.maximum ws 0
  have hm : 0 < m := WeightMaximum.positive ws ht
  have hbound : ∀ w ∈ ws, w ≤ m := (WeightMaximum.bounds ws 0).2
  iintro Hcredit
  iapply Program.twp_open E ws
  twp_bind pl(&Occil.Weighted.validWeights &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedValidation.twp_validWeights E ws ht
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.length &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_length E (fun n : ℕ => Val.int n) ws
  iintro %v %hv
  subst v
  iterate 2 twp_pure
  twp_bind pl(&Program.maximum &(listVal (fun n : ℕ => Val.int n) ws).fst #0)
  iapply tglWp_wand
  isplitl []
  · iapply twp_maximum E ws 0
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.sumInts &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedChoice.twp_sumInts E ws
  iintro %v %hv
  subst v
  twp_bind pl(&Occil.Weighted.integerPower #2 #19)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedIntegerPower.twp_integerPower E 2 19
  iintro %v %hv
  subst v
  twp_pure
  isimp only [Exp.ofVal]
  twp_bind pl(#int ((524288 : ℤ) * ws.length) <= #int (ws.sum : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply KnownIntegerComparison.twp_le E (524288 * ws.length) ws.sum
      (decide (2 ^ 19 * ws.length ≤ ws.sum)) (dense_test ws)
  iintro %v %hv
  subst v
  by_cases hd : 2 ^ 19 * ws.length ≤ ws.sum
  · rw [decide_eq_true hd]
    iterate 2 twp_pure
    iapply twp_dense E ws m ht hm hbound F $$ Hcredit
  · have hfit : ∀ w ∈ ws, w < 2 ^ 32 := Or.resolve_left hwords hd
    rw [decide_eq_false hd]
    iterate 2 twp_pure
    twp_bind pl(&Program.pack &(listVal (fun n : ℕ => Val.int n) ws).fst #0 #0 #0 #0)
    iapply tglWp_wand
    isplitl []
    · iapply twp_pack E ws hfit 0 0 0 0
    iintro %v %hv
    simp only [packVal, pow_zero, one_mul, zero_add] at hv
    subst v
    iterate 7 twp_pure
    iapply twp_packed E ws m ht hm hbound hfit F $$ Hcredit

/-- Exact categorical sampling on the source's complete dense-or-packed input domain. -/
theorem succinctChoice_distSpec (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (hwords : Admissible ws) :
    IsDistSpec (GF := GF) E pl(&Occil.WeightedVariants.succinctChoice
      &(listVal (fun n : ℕ => Val.int n) ws).fst #()) (WeightedChoice.law ws)
      (fun i : ℕ => Val.int (i : ℤ)) where
  spec F _ := wand_entails (twp_succinctChoice E ws (NeZero.pos ws.sum) hwords F)

end specification

end

end SampLib.SuccinctChoice
