import SampLib.Distributions.SystematicPPS
import SampLib.WeightedValidation
import SampLib.Syntax.InclusionSystematic
import Samplers.Weighted.Reservoir

/-! # Systematic sampling with prescribed inclusion probabilities

A single uniform shift drives the deterministic scan, preserving its joint law.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.InclusionSystematic

noncomputable section

open Program

private theorem capacity_test (count total : ℤ) (w : ℕ) (h : count * w ≤ total) :
    decide (total < count * (w : ℤ)) = false := decide_eq_false (not_lt.mpr h)

private theorem population_test (count size : ℕ) (h : count ≤ size) :
    decide ((size : ℤ) < count) = false := decide_eq_false (by exact_mod_cast not_lt.mpr h)

private theorem nonzero_test (count : ℕ) (h : count ≠ 0) :
    ((count : ℤ) == 0) = false := beq_eq_false_iff_ne.mpr (by exact_mod_cast h)

private theorem cast_capacity (count total : ℕ) (ws : List ℕ)
    (h : ∀ w ∈ ws, count * w ≤ total) : ∀ w ∈ ws, (count : ℤ) * w ≤ total :=
  fun w hw => by exact_mod_cast h w hw

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] GeneralSyntax.length_openRec GeneralSyntax.length_closeRec
  WeightedValidation.validWeights_openRec WeightedValidation.validWeights_closeRec
  WeightedValidation.sumInts_openRec WeightedValidation.sumInts_closeRec
  UniformInt.uniformInt_openRec UniformInt.uniformInt_closeRec

private theorem twp_scan (E : CoPset) (ws : List ℕ)
    (count total ticket before label : ℤ) (hcap : ∀ w ∈ ws, count * w ≤ total) :
    ⊢ tglWp E pl(&(scan count total ticket) &(listVal (fun n : ℕ => Val.int n) ws).fst
        #int before #int label)
      (fun v => iprop(⌜v = listVal Val.int
        (SystematicPPS.select count total ticket ws before label)⌝)) := by
  induction ws generalizing before label with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    ipureintro
    exact Val.ext rfl
  | cons w ws ih =>
    have hw := hcap w (by simp)
    have htail : ∀ a ∈ ws, count * a ≤ total := fun a ha => hcap a (by simp [ha])
    simp only [listVal]
    twp_pures
    rw [capacity_test count total w hw]
    twp_pures
    by_cases h : (before + ticket) / total < (before + count * w + ticket) / total
    · rw [decide_eq_true h]
      iterate 3 twp_pure
      twp_bind pl(&(scan count total ticket) &(listVal (fun n : ℕ => Val.int n) ws).fst
        #int (before + count * w) #int (label + 1))
      iapply tglWp_wand
      isplitl []
      · iapply ih (before + count * w) (label + 1) htail
      iintro %v %hv
      subst v
      simp only [Exp.ofVal]
      let result : Val rT := .inr (.pair (.int label)
        (listVal Val.int (SystematicPPS.select count total ticket ws
          (before + count * w) (label + 1))))
      iapply (tglWp_value_of_toVal (Val.toVal?_fst result))
      ipureintro
      simp only [result, SystematicPPS.select, ite_eq_left h, listVal]

    · rw [decide_eq_false h]
      iterate 3 twp_pure
      twp_bind pl(&(scan count total ticket) &(listVal (fun n : ℕ => Val.int n) ws).fst
        #int (before + count * w) #int (label + 1))
      iapply tglWp_wand
      isplitl []
      · iapply ih (before + count * w) (label + 1) htail
      iintro %v %hv
      subst v
      iapply (tglWp_value (v := listVal Val.int
        (SystematicPPS.select count total ticket ws (before + count * w) (label + 1))))
      ipureintro
      simp only [SystematicPPS.select, ite_eq_right h]

private theorem int_beq {rT : Type} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

private theorem twp_zero (E : CoPset) (ws : List ℕ) (F : List ℤ → ℝ≥0∞) :
    ⊢ ↯ (F []) -∗
      tglWp E pl(&Occil.Weighted.inclusionSystematic
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

/-- Requesting no items returns the empty sample even for an empty or zero-mass population. -/
theorem inclusionSystematic_zero_distSpec (E : CoPset) (ws : List ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.Weighted.inclusionSystematic
      &(listVal (fun n : ℕ => Val.int n) ws).fst #0)
      (MeasureTheory.Measure.dirac ([] : List ℤ)) (listVal Val.int) where
  spec F _ := by
    simpa only [MeasureTheory.lintegral_dirac] using wand_entails (twp_zero E ws F)

variable [ProbLangDist.IsUniformInt rT]

/-- CTE follows one uniform shift and the deterministic cumulative-weight scan. -/
theorem twp_inclusionSystematic (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (count : ℕ) (hcount : count ≤ ws.length)
    (hcap : ∀ w ∈ ws, count * w ≤ ws.sum) (F : List ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ xs, F xs ∂SystematicPPS.law ws count) -∗
      tglWp E pl(&Occil.Weighted.inclusionSystematic
        &(listVal (fun n : ℕ => Val.int n) ws).fst #int (count : ℤ))
        (fun v => iprop(∃ xs : List ℤ, ⌜v = listVal Val.int xs⌝ ∗ ↯ (F xs))) := by
  by_cases hz : count = 0
  · subst count
    simpa only [SystematicPPS.law_zero, MeasureTheory.lintegral_dirac,
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
    rw [population_test count ws.length hcount]
    simp only [Bool.or_false]
    twp_pures
    rw [int_beq, nonzero_test count hz]
    twp_pure
    twp_bind pl(&Occil.Weighted.validWeights &(listVal (fun n : ℕ => Val.int n) ws).fst)
    iapply tglWp_wand
    isplitl []
    · iapply WeightedValidation.twp_validWeights E ws (NeZero.pos ws.sum)
    iintro %v %hv
    subst v
    twp_pure
    twp_bind pl(&Occil.sumInts &(listVal (fun n : ℕ => Val.int n) ws).fst)
    iapply tglWp_wand
    isplitl []
    · iapply WeightedChoice.twp_sumInts E ws
    iintro %v %hv
    subst v
    twp_pure
    twp_bind pl(&Occil.uniformInt #int (ws.sum : ℤ))
    isimp only [SystematicPPS.expectation] at Hcredit
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply UniformInt.twp_uniformInt E ws.sum (NeZero.pos ws.sum)
        (fun t => F (SystematicPPS.select count ws.sum t ws 0 0)) $$ Hcredit
    iintro %v ⟨%t, %hv, %ht, Hcredit⟩
    subst v
    iterate 2 twp_pure
    have hscan := twp_scan (rT := rT) (GF := GF) E ws count ws.sum t 0 0
      (cast_capacity count ws.sum ws hcap)
    twp_bind pl(&(scan (count : ℤ) (ws.sum : ℤ) (t : ℤ))
      &(listVal (fun n : ℕ => Val.int n) ws).fst #int (0 : ℤ) #int (0 : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply hscan
    iintro %v %hv
    subst v
    iapply (tglWp_value (v := listVal Val.int (SystematicPPS.select count ws.sum t ws 0 0)))
    iexists (SystematicPPS.select count ws.sum t ws 0 0)
    iframe Hcredit
    itrivial

/-- Exact joint systematic-PPS law, with the requested cardinality and prescribed marginals. -/
theorem inclusionSystematic_distSpec (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (count : ℕ) (hcount : count ≤ ws.length)
    (hcap : ∀ w ∈ ws, count * w ≤ ws.sum) :
    IsDistSpec (GF := GF) E pl(&Occil.Weighted.inclusionSystematic
      &(listVal (fun n : ℕ => Val.int n) ws).fst #int (count : ℤ))
      (SystematicPPS.law ws count) (listVal Val.int) where
  spec F _ := wand_entails (twp_inclusionSystematic E ws count hcount hcap F)

end specification

end

end SampLib.InclusionSystematic
