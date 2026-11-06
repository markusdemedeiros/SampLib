import SampLib.ListEncoding
import SampLib.Samplers.UniformInt
import Samplers.Discrete
import Metrology.Iris.LocalBI

/-! # Cumulative weighted choice

A uniform rank is partitioned into consecutive blocks, one per category.
Zero-weight categories have empty blocks. Weights are natural numbers, encoded
as nonnegative ProbLang integers.
-/

open ProbLang Finset
open scoped ENNReal

namespace SampLib.WeightedChoice

noncomputable section

section distribution

open MeasureTheory

/-- The category containing a rank in the concatenation of the weight blocks. -/
def category : List ℕ → ℕ → ℕ
  | [], _ => 0
  | w :: ws, k => if k < w then 0 else category ws (k - w) + 1

/-- Unnormalized categorical expectation, with one summand per list position. -/
def weightedSum : List ℕ → (ℕ → ℝ≥0∞) → ℝ≥0∞
  | [], _ => 0
  | w :: ws, F => w * F 0 + weightedSum ws (fun i => F (i + 1))

/-- Each block contributes its length times the category's continuation credit. -/
theorem rank_partition (ws : List ℕ) (F : ℕ → ℝ≥0∞) :
    ∑ k ∈ range ws.sum, F (category ws k) = weightedSum ws F := by
  induction ws generalizing F with
  | nil => simp [weightedSum]
  | cons w ws IH =>
    rw [List.sum_cons, sum_range_add]
    have first : (∑ k ∈ range w, F (category (w :: ws) k)) = w * F 0 := by
      simp only [category]
      calc
        _ = ∑ k ∈ range w, F 0 :=
          sum_congr rfl fun k hk => by rw [ite_eq_left (mem_range.mp hk)]
        _ = _ := by simp [nsmul_eq_mul]
    rw [first]
    simp only [category, Nat.not_lt.mpr (Nat.le_add_right w _), ↓reduceIte,
      Nat.add_sub_cancel_left]
    rw [IH (fun i => F (i + 1))]
    rfl

/-- The categorical law: a category has probability its weight divided by the total. -/
def law (ws : List ℕ) : Measure ℕ :=
  (UniformInt.law ws.sum).map (category ws)

instance (ws : List ℕ) [NeZero ws.sum] : IsProbabilityMeasure (law ws) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Normalized categorical expectation; credits may be infinite. -/
theorem lintegral_law (ws : List ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ i, F i ∂law ws = weightedSum ws F / ws.sum := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    UniformInt.lintegral_law, rank_partition]

@[simp] theorem weightedSum_zero (ws : List ℕ) : weightedSum ws (fun _ => 0) = 0 := by
  induction ws with
  | nil => rfl
  | cons w ws IH => simp [weightedSum, IH]

private theorem weightedSum_singleton (ws : List ℕ) (i : ℕ) :
    weightedSum ws (fun j => if j = i then 1 else 0) = (ws[i]?.getD 0 : ℝ≥0∞) := by
  induction ws generalizing i with
  | nil => simp [weightedSum]
  | cons w ws IH =>
    cases i with
    | zero => simp [weightedSum]
    | succ i => simpa [weightedSum] using IH i

/-- Zero and out-of-range weights have zero probability. -/
theorem law_singleton (ws : List ℕ) (i : ℕ) :
    law ws {i} = (ws[i]?.getD 0 : ℝ≥0∞) / ws.sum := by
  rw [← lintegral_indicator_one (measurableSet_singleton i)]
  simpa [Set.indicator, weightedSum_singleton] using
    lintegral_law ws (fun j => if j = i then 1 else 0)

end distribution

private def check {rT : Type _} : Exp rT := pl%
  rec valid xs := case! xs
    | inl(u) => #true
    | inr(p) => if fst(p) < #0 then #false else valid (snd(p))

private def select {rT : Type _} : Exp rT := pl%
  rec go xs value i := case! xs
    | inl(u) => fail
    | inr(p) => if value < fst(p) then i else
      go (snd(p)) (value - fst(p)) (i + #1)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_check (E : CoPset) (ws : List ℕ) :
    ⊢ tglWp E pl(&check &(listVal (fun n : ℕ => Val.int n) ws).fst)
      (fun v : Val rT => iprop(⌜v = Val.bool true⌝)) := by
  induction ws with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    itrivial
  | cons w ws IH =>
    simp only [listVal]
    iterate 8 twp_pure
    exact IH

theorem twp_sumInts (E : CoPset) (ws : List ℕ) :
    ⊢ tglWp E pl(&Occil.sumInts &(listVal (fun n : ℕ => Val.int n) ws).fst)
      (fun v : Val rT => iprop(⌜v = Val.int (ws.sum : ℤ)⌝)) := by
  induction ws with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    itrivial
  | cons w ws IH =>
    simp only [listVal]
    iterate 5 twp_pure
    twp_bind pl(&Occil.sumInts &(listVal (fun n : ℕ => Val.int n) ws).fst)
    iapply tglWp_wand
    isplitl []
    · iapply IH
    iintro %v %hv
    subst v
    twp_pures
    twp_value
    imodintro
    ipureintro
    apply Val.ext
    simp [List.sum_cons]

private theorem twp_select (E : CoPset) (ws : List ℕ) (k offset : ℕ)
    (hk : k < ws.sum) :
    ⊢ tglWp E pl(&select &(listVal (fun n : ℕ => Val.int n) ws).fst
        #int (k : ℤ) #int (offset : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int ((offset + category ws k : ℕ) : ℤ)⌝)) := by
  induction ws generalizing k offset with
  | nil => simp at hk
  | cons w ws IH =>
    simp only [listVal]
    twp_pures
    by_cases h : k < w
    · rw [show decide ((k : ℤ) < (w : ℤ)) = true by exact_mod_cast decide_eq_true h]
      twp_pures
      twp_value
      imodintro
      ipureintro
      simp [category, h]
    · rw [show decide ((k : ℤ) < (w : ℤ)) = false by
        exact decide_eq_false (by omega)]
      iterate 5 twp_pure
      rw [← Nat.cast_sub (Nat.le_of_not_gt h), ← Nat.cast_add_one]
      have output : offset + category (w :: ws) k =
          (offset + 1) + category ws (k - w) := by simp [category, h]; omega
      rw [output]
      exact IH (k - w) (offset + 1) (by simp only [List.sum_cons] at hk; omega)

variable [ProbLangDist.IsUniformInt rT]

/-- CTE specification for nonnegative weights of positive total. -/
theorem twp_weightedChoice (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ i, F i ∂law ws) -∗
      tglWp E pl(&Occil.weightedChoice &(listVal (fun n : ℕ => Val.int n) ws).fst)
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ ↯ (F i))) := by
  iintro Hcredit
  twp_pure
  twp_pure
  twp_bind pl(&check &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_check E ws
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.sumInts &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_sumInts E ws
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.uniformInt #int (ws.sum : ℤ))
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply UniformInt.twp_uniformInt E ws.sum (NeZero.pos ws.sum)
      (fun k => F (category ws k))
    rw [rank_partition, ← lintegral_law]
    iexact Hcredit
  iintro %v ⟨%k, %hv, %hk, Hcredit⟩
  subst v
  twp_pure
  twp_pure
  twp_bind pl(&select &(listVal (fun n : ℕ => Val.int n) ws).fst #int (k : ℤ) #0)
  iapply tglWp_wand
  isplitl []
  · iapply twp_select E ws k 0 hk
  iintro %v %hv
  iapply (tglWp_value (v := v))
  iexists category ws k
  iframe Hcredit
  ipureintro
  simpa only [Nat.zero_add] using hv

/-- The selected index has probability equal to its weight divided by the total. -/
theorem weightedChoice_distSpec (E : CoPset) (ws : List ℕ) [NeZero ws.sum] :
    IsDistSpec (GF := GF) E
      pl(&Occil.weightedChoice &(listVal (fun n : ℕ => Val.int n) ws).fst)
      (law ws) (fun i => Val.int (i : ℤ)) where
  spec F _ := wand_entails (twp_weightedChoice E ws F)

end specification

end

end SampLib.WeightedChoice
