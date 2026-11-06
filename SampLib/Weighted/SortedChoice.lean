import SampLib.Weighted.Support.SortedChoice
import SampLib.Weighted.FastLoadedDiceRoller

/-! # Exact categorical sampling by sorted dyadic envelope rejection

The source groups positions `2^k, …, 2^(k+1)-1` from the heavy end of a monotone weight
list, draws a group by FLDR with the envelope masses, proposes a uniform position in it and
accepts with probability weight/envelope.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.SortedChoice

noncomputable section

private theorem singleton_test {rT : Type} [BEq rT] (n : ℕ) :
    ((BaseLit.int (n : ℤ) : BaseLit rT) == .int 1) = decide (n = 1) := by
  change ((n : ℤ) == (1 : ℤ)) = decide (n = 1)
  by_cases h : n = 1 <;> simp [h]

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open scoped SampLib.SortedChoice.Program

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec Program.weights_closeRec
  WeightedValidation.validWeights_openRec WeightedValidation.validWeights_closeRec
  GeneralSyntax.length_openRec GeneralSyntax.length_closeRec

omit [ProbLangDist.IsUniformInt rT] in
/-- The source orients the list by comparing its two end weights. -/
private theorem twp_ascending (E : CoPset) (ws : List ℕ) (hn : 0 < ws.length) :
    ⊢ tglWp E pl(&Occil.getAt &(listVal (fun n : ℕ => Val.int n) ws).fst #0 <=
        &Occil.getAt &(listVal (fun n : ℕ => Val.int n) ws).fst (#int (ws.length : ℤ) - #1))
      (fun v : Val rT => iprop(⌜v = Val.bool (SortedWeights.ascending ws)⌝)) := by
  have hlast : ws.length - 1 < ws.length := by omega
  twp_pure
  rw [show (ws.length : ℤ) - 1 = ((ws.length - 1 : ℕ) : ℤ) by omega]
  twp_bind pl(&Occil.getAt &(listVal (fun n : ℕ => Val.int n) ws).fst
    #int ((ws.length - 1 : ℕ) : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_getAt E (fun n : ℕ => Val.int n) ws ⟨_, hlast⟩
  iintro %v %hv
  subst v
  twp_bind pl(&Occil.getAt &(listVal (fun n : ℕ => Val.int n) ws).fst #int ((0 : ℕ) : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_getAt E (fun n : ℕ => Val.int n) ws ⟨0, hn⟩
  iintro %v %hv
  subst v
  twp_pures
  twp_value
  imodintro
  ipureintro
  apply Val.ext
  simp [SortedWeights.ascending, List.getElem?_eq_getElem hn, List.getElem?_eq_getElem hlast]

/-- Validation, orientation, the monotonicity check and the envelope table precede the loop. -/
theorem twp_sortedChoice (E : CoPset) (ws : List ℕ) (ht : 0 < ws.sum)
    (hsorted : SortedWeights.Sorted ws) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) -∗
      tglWp E pl(&Occil.WeightedVariants.sortedChoice
        &(listVal (fun n : ℕ => Val.int n) ws).fst #())
        (fun v => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ ↯ (F i))) := by
  have hn := List.length_pos_of_sum_ne_zero ws ht.ne'
  have hs := SortedWeights.chosen_order ws hsorted
  iintro Hcredit
  iapply Program.twp_open E ws
  twp_bind pl(&Occil.length &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_length E (fun n : ℕ => Val.int n) ws
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.Weighted.validWeights &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedValidation.twp_validWeights E ws ht
  iintro %v %hv
  subst v
  twp_pures
  by_cases h1 : ws.length = 1
  · obtain ⟨w, rfl⟩ := List.length_eq_one_iff.mp h1
    rw [singleton_test, decide_eq_true h1]
    twp_pures
    twp_value
    imodintro
    iexists 0
    have hc : KnuthYao.certain [w] [w].sum = some 0 := by simp [KnuthYao.certain]
    isimp only [KnuthYao.certain_expectation [w] ht 0 hc F] at Hcredit
    iframe Hcredit
    itrivial
  · rw [singleton_test, decide_eq_false h1]
    twp_pure
    twp_bind pl(&Occil.getAt &(listVal (fun n : ℕ => Val.int n) ws).fst #0 <=
      &Occil.getAt &(listVal (fun n : ℕ => Val.int n) ws).fst (#int (ws.length : ℤ) - #1))
    iapply tglWp_wand
    isplitl []
    · iapply twp_ascending E ws hn
    iintro %v %hv
    subst v
    iterate 2 twp_pure
    twp_bind pl(&(Program.check (SortedWeights.ascending ws))
      &(listVal (fun n : ℕ => Val.int n) ws).fst)
    iapply tglWp_wand
    isplitl []
    · iapply twp_check E ws _ hs
    iintro %v %hv
    subst v
    iterate 2 twp_pure
    twp_bind pl(&(Program.groups ws (SortedWeights.ascending ws)) #1)
    iapply tglWp_wand
    isplitl []
    · iapply twp_groups E ws (SortedWeights.ascending ws)
    iintro %v %hv
    subst v
    iterate 2 twp_pure
    have : NeZero ws.sum := ⟨ht.ne'⟩
    have : NeZero (envelopes ws (SortedWeights.ascending ws)).sum :=
      ⟨(envelopes_pos ws _ ht hs).ne'⟩
    iapply twp_loop E ws (SortedWeights.ascending ws) hs
      (FastLoadedDice.fastLoadedDiceRoller_distSpec E _) F $$ Hcredit

/-- Exact categorical sampling for every monotone natural-weight list of positive total. -/
theorem sortedChoice_distSpec (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (hsorted : SortedWeights.Sorted ws) :
    IsDistSpec (GF := GF) E pl(&Occil.WeightedVariants.sortedChoice
      &(listVal (fun n : ℕ => Val.int n) ws).fst #()) (WeightedChoice.law ws)
      (fun i : ℕ => Val.int (i : ℤ)) where
  spec F _ := wand_entails (twp_sortedChoice E ws (NeZero.pos ws.sum) hsorted F)

end

end SampLib.SortedChoice
