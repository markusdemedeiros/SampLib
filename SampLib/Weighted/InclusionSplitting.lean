import SampLib.Weighted.Laws.SplittingPPSInputLaw
import SampLib.Weighted.Laws.SplittingPPSCoin
import SampLib.Weighted.Support.SplittingPPS
import SampLib.Core.SupportedSpec

/-! # Exact fixed-size inclusion sampling by Deville–Tillé splitting -/

open ProbLang
open scoped ENNReal

namespace SampLib.InclusionSplitting

open SplittingPPS

noncomputable section

private def lowIndex {size count : ℕ} (s : State size count) (hc : 0 < count)
    (hs : count < size) : Fin s.items.length := ⟨size - count - 1, by rw [s.length_eq]; omega⟩

private def highIndex {size count : ℕ} (s : State size count) (hc : 0 < count)
    (hs : count < size) : Fin s.items.length := ⟨size - count, by rw [s.length_eq]; omega⟩

private theorem low_cast {size count : ℕ} (s : State size count) (hc : 0 < count)
    (hs : count < size) : (size : ℤ) - count - 1 = ((lowIndex s hc hs).val : ℤ) := by
  simp only [lowIndex]
  omega

private theorem high_cast {size count : ℕ} (s : State size count) (hc : 0 < count)
    (hs : count < size) : (size : ℤ) - count = ((highIndex s hc hs).val : ℤ) := by
  simp only [highIndex]
  omega

private theorem low_lookup {size count : ℕ} (s : State size count) (hc : 0 < count)
    (hs : count < size) : (s.items.get (lowIndex s hc hs)).1 = s.low := by
  have hi : size - count - 1 < s.items.length := (lowIndex s hc hs).isLt
  simp only [State.low, lowIndex, List.get_eq_getElem, List.getElem?_eq_getElem hi,
    Option.getD_some]

private theorem high_lookup {size count : ℕ} (s : State size count) (hc : 0 < count)
    (hs : count < size) : (s.items.get (highIndex s hc hs)).1 = s.high := by
  have hi : size - count < s.items.length := (highIndex s hc hs).isLt
  simp only [State.high, highIndex, List.get_eq_getElem, List.getElem?_eq_getElem hi,
    Option.getD_some]

private theorem complement_cast {size count : ℕ} (s : State size count) (hc : 0 < count)
    (hs : count < size) : (s.denominator : ℤ) - s.low = ((s.denominator - s.low : ℕ) : ℤ) :=
  (Nat.cast_sub (s.boundaries hc hs).1.le).symm

private theorem amount_test {size count : ℕ} (s : State size count) (hc : 0 < count)
    (hs : count < size) : decide ((s.amount : ℤ) ≤ 0) = false :=
  decide_eq_false (by exact_mod_cast not_le.mpr (s.amount_bounds hc hs).1)

private theorem population_test (count size : ℕ) (h : count ≤ size) :
    decide ((size : ℤ) < count) = false := decide_eq_false (by exact_mod_cast not_lt.mpr h)

private theorem nonzero_test (count : ℕ) (h : count ≠ 0) :
    ((count : ℤ) == 0) = false := beq_eq_false_iff_ne.mpr (by exact_mod_cast h)

private theorem int_beq {rT : Type} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ListAccess.getAt_openRec ListAccess.getAt_closeRec
  RationalCoin.rationalCoin_openRec RationalCoin.rationalCoin_closeRec
  SplittingPPS.insert_openRec SplittingPPS.insert_closeRec
  Program.select_openRec Program.select_closeRec
  GeneralSyntax.length_openRec GeneralSyntax.length_closeRec
  WeightedValidation.validWeights_openRec WeightedValidation.validWeights_closeRec
  WeightedValidation.sumInts_openRec WeightedValidation.sumInts_closeRec

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_min (E : CoPset) (a b : ℕ) :
    ⊢ tglWp E pl(if #int (a : ℤ) < #int (b : ℤ) then #int (a : ℤ) else #int (b : ℤ))
      (fun v => iprop(⌜v = Val.int (min a b : ℕ)⌝)) := by
  twp_pure
  by_cases h : (a : ℤ) < b
  · rw [decide_eq_true h]
    twp_pures
    twp_value
    imodintro
    ipureintro
    rw [min_eq_left (by omega)]
  · rw [decide_eq_false h]
    twp_pures
    twp_value
    imodintro
    ipureintro
    rw [min_eq_right (by omega)]

/-- Each split executes two lookups, one supported Bernoulli draw, and one deterministic branch. -/
private theorem twp_round (E : CoPset) {size count : ℕ} (hc : 0 < count) (hs : count < size)
    (s : State size count) (F : List ℤ → ℝ≥0∞)
    (hrec : ∀ hn : s.amount < s.denominator,
      ⊢ ↯ (∫⁻ xs, F xs ∂law hc hs (s.next hc hs hn)) -∗
        tglWp E pl(&(Program.loop (size : ℤ) (count : ℤ))
          &(listVal itemVal (s.next hc hs hn).items).fst
          #int ((s.next hc hs hn).denominator : ℤ))
          (fun v : Val rT => iprop(∃ xs : List ℤ, ⌜v = listVal Val.int xs⌝ ∗ ↯ (F xs)))) :
    ⊢ ↯ (∫⁻ xs, F xs ∂law hc hs s) -∗
      tglWp E pl(&(Program.loop (size : ℤ) (count : ℤ)) &(listVal itemVal s.items).fst
        #int (s.denominator : ℤ))
        (fun v : Val rT => iprop(∃ xs : List ℤ, ⌜v = listVal Val.int xs⌝ ∗ ↯ (F xs))) := by
  have hcoin := RationalCoin.rationalCoin_distSpec (rT := rT) (GF := GF) E
    (s.amount : ℤ) (s.denominator : ℤ) (by omega) (by exact_mod_cast s.positive)
    (by exact_mod_cast (s.amount_bounds hc hs).2.1)
  iintro Hcredit
  iterate 5 twp_pure
  rw [low_cast s hc hs]
  twp_bind pl(&Occil.getAt &(listVal itemVal s.items).fst #int ((lowIndex s hc hs).val : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_getAt E itemVal s.items (lowIndex s hc hs)
  iintro %v %hv
  subst v
  iterate 2 twp_pure
  rw [high_cast s hc hs]
  twp_bind pl(&Occil.getAt &(listVal itemVal s.items).fst #int ((highIndex s hc hs).val : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_getAt E itemVal s.items (highIndex s hc hs)
  iintro %v %hv
  subst v
  iterate 6 twp_pure
  rw [low_lookup s hc hs, high_lookup s hc hs, complement_cast s hc hs]
  twp_bind pl(if #int ((s.denominator - s.low : ℕ) : ℤ) < #int (s.high : ℤ)
    then #int ((s.denominator - s.low : ℕ) : ℤ) else #int (s.high : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_min E (s.denominator - s.low) s.high
  iintro %v %hv
  subst v
  iterate 2 twp_pure
  rw [← State.amount]
  rw [amount_test s hc hs]
  twp_pure
  twp_bind pl(&Occil.rationalCoin #int (s.amount : ℤ) #int (s.denominator : ℤ))
  isimp only [← split_expectation s hc hs F, splitBias] at Hcredit
  iapply (hcoin.wp_supported
      (fun b => b = true ∨ s.amount < s.denominator)
      (Set.to_countable _).measurableSet (split_support s hc hs)
      (branchCredit s hc hs F) (measurable_of_countable _) _) $$ Hcredit
  iintro %b %hb Hcredit
  cases b with
  | true =>
    iterate 2 twp_pure
    rw [high_cast s hc hs]
    twp_bind pl(&Program.select &(listVal itemVal s.items).fst #int ((size - count : ℕ) : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply twp_select E s.items (size - count)
    iintro %v %hv
    subst v
    iapply (tglWp_value (v := listVal Val.int ((s.items.drop (size - count)).map Prod.snd)))
    iexists s.topLabels
    isplit
    · ipureintro
      rfl
    isimp only [branchCredit, ite_true] at Hcredit
    iexact Hcredit
  | false =>
    have hn := hb.resolve_left Bool.false_ne_true
    isimp only [branchCredit, Bool.false_eq_true, ite_false, dite_eq_left hn] at Hcredit
    iterate 4 twp_pure
    rw [high_cast s hc hs]
    twp_bind pl(&(Program.adjust (s.amount : ℤ)) &(listVal itemVal s.items).fst
      #int ((size - count : ℕ) : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply twp_adjust E s.amount ((size - count : ℕ) : ℤ) s.items
        (by simpa only [Int.toNat_natCast] using s.amount_le_top hc hs)
    iintro %v %hv
    subst v
    isimp only [Int.toNat_natCast]
    rw [← Nat.cast_sub (s.amount_bounds hc hs).2.1]
    ihave Hnext := hrec hn $$ Hcredit
    isimp only [State.next, Exp.ofVal] at Hnext
    isimp only [Exp.ofVal]
    iexact Hnext

/-- Finite denominator descent accounts for every possible rejection. -/
theorem twp_loop (E : CoPset) {size count : ℕ} (hc : 0 < count) (hs : count < size)
    (s : State size count) (F : List ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ xs, F xs ∂law hc hs s) -∗
      tglWp E pl(&(Program.loop (size : ℤ) (count : ℤ)) &(listVal itemVal s.items).fst
        #int (s.denominator : ℤ))
        (fun v : Val rT => iprop(∃ xs : List ℤ, ⌜v = listVal Val.int xs⌝ ∗ ↯ (F xs))) := by
  exact twp_round E hc hs s F (fun hn => twp_loop E hc hs (s.next hc hs hn) F)
termination_by s.denominator

decreasing_by exact s.next_lt hc hs hn

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_zero (E : CoPset) (ws : List ℕ) (F : List ℤ → ℝ≥0∞) :
    ⊢ ↯ (F []) -∗
      tglWp E pl(&Occil.Weighted.inclusionSplitting
        &(listVal (fun n : ℕ => Val.int n) ws).fst #0)
        (fun v => iprop(∃ xs : List ℤ, ⌜v = listVal Val.int xs⌝ ∗ ↯ (F xs))) := by
  iintro Hcredit
  iapply Program.twp_open E (listVal (fun n : ℕ => Val.int n) ws) 0
  twp_bind pl(&Occil.length &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_length E _ ws
  iintro %v %hv
  subst v
  twp_pures
  twp_value
  imodintro
  iexists ([] : List ℤ)
  iframe Hcredit
  ipureintro
  exact Val.ext rfl

omit [ProbLangDist.IsUniformInt rT] in
/-- A zero-size request returns no labels even for an empty or zero-total population. -/
theorem inclusionSplitting_zero_distSpec (E : CoPset) (ws : List ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.Weighted.inclusionSplitting
      &(listVal (fun n : ℕ => Val.int n) ws).fst #0)
      (MeasureTheory.Measure.dirac ([] : List ℤ)) (listVal Val.int) where
  spec F _ := by
    simpa only [MeasureTheory.lintegral_dirac] using wand_entails (twp_zero E ws F)

/-- Validation and stable preprocessing lead to a full selection or a finite splitting chain. -/
theorem twp_inclusionSplitting (E : CoPset) (ws : List ℕ) (count : ℕ) (ht : 0 < ws.sum)
    (hc : count ≤ ws.length) (hcap : ∀ w ∈ ws, count * w ≤ ws.sum) (F : List ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ xs, F xs ∂inputLaw ws count ht hc hcap) -∗
      tglWp E pl(&Occil.Weighted.inclusionSplitting
        &(listVal (fun n : ℕ => Val.int n) ws).fst #int (count : ℤ))
        (fun v => iprop(∃ xs : List ℤ, ⌜v = listVal Val.int xs⌝ ∗ ↯ (F xs))) := by
  by_cases hz : count = 0
  · subst count
    simpa only [inputLaw, dite_true, MeasureTheory.lintegral_dirac,
      Exp.ofVal, Nat.cast_zero] using twp_zero (rT := rT) (GF := GF) E ws F
  · iintro Hcredit
    iapply Program.twp_open E (listVal (fun n : ℕ => Val.int n) ws) count
    twp_bind pl(&Occil.length &(listVal (fun n : ℕ => Val.int n) ws).fst)
    iapply tglWp_wand
    isplitl []
    · iapply twp_length E _ ws
    iintro %v %hv
    subst v
    twp_pures
    rw [population_test count ws.length hc]
    simp only [Bool.or_false]
    twp_pures
    rw [int_beq, nonzero_test count hz]
    twp_pure
    twp_bind pl(&Occil.Weighted.validWeights &(listVal (fun n : ℕ => Val.int n) ws).fst)
    iapply tglWp_wand
    isplitl []
    · iapply WeightedValidation.twp_validWeights E ws ht
    iintro %v %hv
    subst v
    twp_pure
    twp_bind pl(&Occil.sumInts &(listVal (fun n : ℕ => Val.int n) ws).fst)
    iapply tglWp_wand
    isplitl []
    · iapply WeightedChoice.twp_sumInts E ws
    iintro %v %hv
    subst v
    twp_pures
    rw [int_beq]
    by_cases hf : count = ws.length
    · subst count
      rw [beq_self_eq_true]
      twp_pure
      twp_bind pl(&(Program.prepare (ws.length : ℤ) (ws.sum : ℤ))
        &(listVal (fun n : ℕ => Val.int n) ws).fst #0)
      iapply tglWp_wand
      isplitl []
      · iapply twp_prepare E ws.length ws.sum ws 0 hcap
      iintro %v %hv
      subst v
      twp_bind pl(&Program.select &(listVal itemVal (prepare ws.length ws 0)).fst #0)
      iapply tglWp_wand
      isplitl []
      · iapply twp_select E (prepare ws.length ws 0) 0
      iintro %v %hv
      subst v
      iapply (tglWp_value (v := listVal Val.int
        (((prepare ws.length ws 0).drop 0).map Prod.snd)))
      iexists ((prepare ws.length ws 0).map Prod.snd)
      isplit
      · ipureintro
        rfl
      isimp only [inputLaw, dite_eq_right hz, lt_self_iff_false, dite_false,
        MeasureTheory.lintegral_dirac] at Hcredit
      iexact Hcredit
    · have hs : count < ws.length := by omega
      rw [beq_eq_false_iff_ne.mpr (by exact_mod_cast hf)]
      iterate 2 twp_pure
      twp_bind pl(&(Program.prepare (count : ℤ) (ws.sum : ℤ))
        &(listVal (fun n : ℕ => Val.int n) ws).fst #0)
      iapply tglWp_wand
      isplitl []
      · iapply twp_prepare E count ws.sum ws 0 hcap
      iintro %v %hv
      subst v
      isimp only [inputLaw, dite_eq_right hz, dite_eq_left hs] at Hcredit
      ihave Hloop := twp_loop E (Nat.pos_of_ne_zero hz) hs
        (State.initial ws count ht hcap) F $$ Hcredit
      isimp only [State.initial, Exp.ofVal] at Hloop
      isimp only [Exp.ofVal]
      iexact Hloop

/-- The exact joint law for every admissible natural-weight population and sample size. -/
theorem inclusionSplitting_distSpec (E : CoPset) (ws : List ℕ) (count : ℕ) (ht : 0 < ws.sum)
    (hc : count ≤ ws.length) (hcap : ∀ w ∈ ws, count * w ≤ ws.sum) :
    IsDistSpec (GF := GF) E pl(&Occil.Weighted.inclusionSplitting
      &(listVal (fun n : ℕ => Val.int n) ws).fst #int (count : ℤ))
      (inputLaw ws count ht hc hcap) (listVal Val.int) where
  spec F _ := wand_entails (twp_inclusionSplitting E ws count ht hc hcap F)

end specification

end

end SampLib.InclusionSplitting
