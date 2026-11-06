import SampLib.Syntax.SortedChoice
import SampLib.Distributions.SortedWeights
import SampLib.Distributions.GroupedEnvelope

/-! # Deterministic preparation of sorted dyadic envelopes -/

open ProbLang

namespace SampLib.SortedChoice

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open scoped SampLib.SortedChoice.Program

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec Program.weights_closeRec

/-- The source accepts every list ordered in its chosen orientation. -/
theorem twp_check (E : CoPset) (ws : List ℕ) (asc : Bool)
    (hs : ws.Pairwise (SortedWeights.Ordered asc)) :
    ⊢ tglWp E pl(&(Program.check asc) &(listVal (fun n : ℕ => Val.int n) ws).fst)
      (fun v : Val rT => iprop(⌜v = Val.bool true⌝)) := by
  induction ws with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    itrivial
  | cons w ws ih =>
    cases ws with
    | nil =>
      simp only [listVal]
      twp_pures
      twp_value
      imodintro
      itrivial
    | cons v ws =>
      have hhead := (List.pairwise_cons.mp hs).1 v (by simp)
      have htail := (List.pairwise_cons.mp hs).2
      cases asc with
      | false =>
        have ht : decide ((w : ℤ) < v) = false := decide_eq_false (by
          change v ≤ w at hhead
          omega)
        simp only [listVal]
        twp_pures
        rw [ht]
        iterate 2 twp_pure
        have hrec := ih htail
        simp only [listVal] at hrec
        iapply hrec
      | true =>
        have ht : decide ((v : ℤ) < w) = false := decide_eq_false (by
          change w ≤ v at hhead
          omega)
        simp only [listVal]
        twp_pures
        rw [ht]
        iterate 2 twp_pure
        have hrec := ih htail
        simp only [listVal] at hrec
        iapply hrec

/-- The source's inclusive group endpoint is the smaller of the length and dyadic endpoint. -/
theorem twp_upper (E : CoPset) (n lower : ℕ) (hl : 0 < lower) :
    ⊢ tglWp E pl(if #int (n : ℤ) < #2 * #int (lower : ℤ) - #1
      then #int (n : ℤ) else #2 * #int (lower : ℤ) - #1)
      (fun v : Val rT => iprop(⌜v = Val.int ((min n (2 * lower - 1) : ℕ) : ℤ)⌝)) := by
  have hc : ((2 * lower - 1 : ℕ) : ℤ) = 2 * (lower : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul]
    rfl
  by_cases h : n < 2 * lower - 1
  · have ht : decide ((n : ℤ) < 2 * lower - 1) = true := decide_eq_true (by omega)
    twp_pures
    rw [ht]
    twp_pures
    twp_value
    imodintro
    ipureintro
    rw [min_eq_left h.le]
  · have ht : decide ((n : ℤ) < 2 * lower - 1) = false := decide_eq_false (by omega)
    twp_pures
    rw [ht]
    twp_pures
    twp_value
    imodintro
    ipureintro
    rw [min_eq_right (by omega), hc]

theorem twp_pivot (E : CoPset) (n k : ℕ) (asc : Bool) (hk : k < n.size) :
    ⊢ tglWp E pl(if #bool asc then #int (n : ℤ) - #int (DyadicGroups.lower k : ℤ)
      else #int (DyadicGroups.lower k : ℤ) - #1)
      (fun v : Val rT => iprop(⌜v = Val.int (SortedWeights.pivot n asc k : ℤ)⌝)) := by
  have hl := DyadicGroups.lower_pos k
  have hn : DyadicGroups.lower k ≤ n := Nat.lt_size.mp hk
  cases asc <;> twp_pures <;> twp_value <;> imodintro <;> ipureintro
  · change Val.int ((DyadicGroups.lower k : ℤ) - 1) =
      Val.int ((DyadicGroups.lower k - 1 : ℕ) : ℤ)
    congr 1
    omega
  · change Val.int ((n : ℤ) - DyadicGroups.lower k) =
      Val.int ((n - DyadicGroups.lower k : ℕ) : ℤ)
    congr 1
    omega

private theorem twp_groups_aux (E : CoPset) (ws : List ℕ) (asc : Bool) (depth k : ℕ)
    (hdepth : k + depth = ws.length.size) :
    ⊢ tglWp E pl(&(Program.groups ws asc) #int (DyadicGroups.lower k : ℤ))
      (fun v : Val rT => iprop(⌜v = listVal (fun n : ℕ => Val.int n)
        ((GroupedEnvelope.masses ws.length (SortedWeights.envelope ws asc)).drop k)⌝)) := by
  induction depth generalizing k with
  | zero =>
    have hk : k = ws.length.size := by omega
    have hstop : ws.length < DyadicGroups.lower k := by
      simpa only [hk, DyadicGroups.lower] using Nat.lt_size_self ws.length
    have ht : decide ((ws.length : ℤ) < DyadicGroups.lower k) = true :=
      decide_eq_true (by exact_mod_cast hstop)
    twp_pures
    rw [ht]
    twp_pures
    twp_value
    imodintro
    ipureintro
    rw [List.drop_of_length_le (by simp [GroupedEnvelope.masses_length, hk])]
    rfl
  | succ depth ih =>
    have hk : k < ws.length.size := by omega
    have hl := DyadicGroups.lower_pos k
    have hn : DyadicGroups.lower k ≤ ws.length := Nat.lt_size.mp hk
    have ht : decide ((ws.length : ℤ) < DyadicGroups.lower k) = false :=
      decide_eq_false (by exact_mod_cast not_lt.mpr hn)
    have hnext : 2 * (DyadicGroups.lower k : ℤ) = (DyadicGroups.lower (k + 1) : ℤ) := by
      simp [DyadicGroups.lower, pow_succ, mul_comm]
    twp_pures
    rw [ht]
    twp_pure
    twp_bind pl(if #int (ws.length : ℤ) < #2 * #int (DyadicGroups.lower k : ℤ) - #1
      then #int (ws.length : ℤ) else #2 * #int (DyadicGroups.lower k : ℤ) - #1)
    iapply tglWp_wand
    isplitl []
    · iapply twp_upper E ws.length (DyadicGroups.lower k) hl
    iintro %v %hv
    subst v
    twp_pure
    twp_bind pl(if #bool asc then #int (ws.length : ℤ) - #int (DyadicGroups.lower k : ℤ)
      else #int (DyadicGroups.lower k : ℤ) - #1)
    iapply tglWp_wand
    isplitl []
    · iapply twp_pivot E ws.length k asc hk
    iintro %v %hv
    subst v
    twp_pure
    twp_bind pl(&Occil.getAt &(listVal (fun n : ℕ => Val.int n) ws).fst
      #int (SortedWeights.pivot ws.length asc k : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply SampLib.twp_getAt E (fun n : ℕ => Val.int n) ws
        ⟨SortedWeights.pivot ws.length asc k, SortedWeights.pivot_lt ws.length k asc hk⟩
    iintro %v %hv
    subst v
    iterate 2 twp_pure
    rw [hnext]
    twp_bind pl(&(Program.groups ws asc) #int (DyadicGroups.lower (k + 1) : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply ih (k + 1) (by omega)
    iintro %v %hv
    subst v
    have hu : min ws.length (2 * DyadicGroups.lower k - 1) =
        DyadicGroups.upper ws.length k := by
      simp [DyadicGroups.upper, DyadicGroups.lower, pow_succ, mul_comm]
    have hwidth : ((min ws.length (2 * DyadicGroups.lower k - 1) : ℕ) : ℤ) -
        DyadicGroups.lower k + 1 = (DyadicGroups.width ws.length k : ℤ) := by
      rw [hu]
      unfold DyadicGroups.width
      rw [Nat.cast_add, Nat.cast_sub (DyadicGroups.lower_le_upper ws.length k hk)]
      rfl
    have hweight : ws.get ⟨SortedWeights.pivot ws.length asc k,
        SortedWeights.pivot_lt ws.length k asc hk⟩ = SortedWeights.envelope ws asc k := by
      simp [SortedWeights.envelope, List.get_eq_getElem,
        List.getElem?_eq_getElem (SortedWeights.pivot_lt ws.length k asc hk)]
    twp_pures
    rw [hwidth, hweight, ← Nat.cast_mul]
    change ⊢ tglWp E (Exp.ofVal (listVal (fun n : ℕ => Val.int n)
      (GroupedEnvelope.mass ws.length (SortedWeights.envelope ws asc) k ::
        (GroupedEnvelope.masses ws.length (SortedWeights.envelope ws asc)).drop (k + 1)))) _
    iapply tglWp_value
    ipureintro
    congr 1
    rw [List.drop_eq_getElem_cons (i := k)
      (l := GroupedEnvelope.masses ws.length (SortedWeights.envelope ws asc))
      (by simpa only [GroupedEnvelope.masses_length] using hk)]
    congr 1
    simp [GroupedEnvelope.masses]

/-- The source materializes precisely the finite list of dyadic envelope masses. -/
theorem twp_groups (E : CoPset) (ws : List ℕ) (asc : Bool) :
    ⊢ tglWp E pl(&(Program.groups ws asc) #1)
      (fun v : Val rT => iprop(⌜v = listVal (fun n : ℕ => Val.int n)
        (GroupedEnvelope.masses ws.length (SortedWeights.envelope ws asc))⌝)) := by
  have h := twp_groups_aux (GF := GF) (rT := rT) E ws asc ws.length.size 0 (by omega)
  simpa only [DyadicGroups.lower, pow_zero, Nat.cast_one, List.drop_zero] using h

end SampLib.SortedChoice
