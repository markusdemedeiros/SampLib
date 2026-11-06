import SampLib.General.Support.ListPartition
import SampLib.Common.Syntax.Shuffle
import SampLib.Common.WeightedValidation
import SampLib.Core.SamplerStep

/-! # A uniform positional permutation, partitioned into prescribed groups

The sizes may be zero; empty observations and entirely empty groups are included.
Repeated observations retain their distinct position multiplicities.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.GroupedPermutation

noncomputable section

variable {α : Type _}
local instance : MeasurableSpace (List (List α)) := ⊤

/-- Consecutive groups of the requested sizes. -/
def groups : List ℕ → List α → List (List α)
  | [], _ => []
  | n :: ns, xs => xs.take n :: groups ns (xs.drop n)

section mathematics

open MeasureTheory

/-- The positional permutation law transported to the prescribed groups. -/
def law (xs : List α) (sizes : List ℕ) : Measure (List (List α)) :=
  (Shuffle.law xs).map (fun σ => groups sizes (Shuffle.output xs σ))

instance (xs : List α) (sizes : List ℕ) : IsProbabilityMeasure (law xs sizes) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Regrouping is a deterministic pushforward; all positional multiplicities survive. -/
theorem expectation (xs : List α) (sizes : List ℕ) (F : List (List α) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ σ, F (groups sizes (Shuffle.output xs σ)) ∂Shuffle.law xs =
      ∫⁻ ys, F ys ∂law xs sizes := by
  rw [law, lintegral_map hF (measurable_of_countable _)]

end mathematics

private def partition {rT : Type _} : Exp rT := pl%
  rec groups xs sizes := case! sizes
    | inl(v) => inl(#())
    | inr(p) =>
      let split := &Occil.General.splitAt xs (fst(p));
      inr((fst(split), groups (snd(split)) (snd(p))))

private def partitionValue {rT : Type _} : Val rT :=
  ⟨partition, .fix (by is_lc), by is_lc⟩

private theorem partitionValue_fst {rT : Type _} :
    (partitionValue (rT := rT)).fst = partition := rfl

private theorem int_beq {rT : Type _} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

private theorem encode_groups {rT : Type _} [ProbLangℝ rT] (encode : α → Val rT)
    (xs : List α) (xss : List (List α)) :
    pl(inr(({(listVal encode xs).fst},
      {Exp.ofVal (listVal (listVal encode) xss)}))) =
      Exp.ofVal (listVal (listVal encode) (xs :: xss)) := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_partition (E : CoPset) (encode : α → Val rT)
    (sizes : List ℕ) (xs : List α) (h : sizes.sum = xs.length) :
    ⊢ tglWp E pl(&(partition (rT := rT)) &(listVal encode xs).fst
        &(listVal (fun n : ℕ => Val.int n) sizes).fst)
      (fun v : Val rT => iprop(⌜v = listVal (listVal encode) (groups sizes xs)⌝)) := by
  induction sizes generalizing xs with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    ipureintro
    exact Val.ext rfl
  | cons n ns IH =>
    have hn : n ≤ xs.length := by simp only [List.sum_cons] at h; omega
    have htail : ns.sum = (xs.drop n).length := by
      rw [List.length_drop]
      simp only [List.sum_cons] at h
      omega
    have hsplit := ListPartition.twp_splitAt (rT := rT) (GF := GF) E encode
      (xs.take n) (xs.drop n)
    rw [List.take_append_drop, List.length_take, Nat.min_eq_left hn] at hsplit
    simp only [listVal]
    rw [← partitionValue_fst]
    twp_step pl(&(partitionValue (rT := rT)).fst &(listVal encode xs).fst)
    simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Var.internal.injEq]
    iterate 5 twp_pure
    simp only [ListPartition.splitAt_openRec]
    twp_bind pl(&Occil.General.splitAt &(listVal encode xs).fst #int (n : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply hsplit
    iintro %v %hv
    subst v
    twp_pure
    twp_pure
    twp_pure
    twp_bind pl(&(partition (rT := rT)) &(listVal encode (xs.drop n)).fst
      &(listVal (fun n : ℕ => Val.int n) ns).fst)
    iapply tglWp_wand
    isplitl []
    · iapply IH (xs.drop n) htail
    iintro %v %hv
    subst v
    twp_pure
    rw [encode_groups]
    iapply (tglWp_value (v := listVal (listVal encode)
      (xs.take n :: groups ns (xs.drop n))))
    ipureintro
    exact Val.ext rfl

variable [ProbLangDist.IsUniformInt rT]

/-- Arbitrary nonnegative group sizes whose sum is the observation count. -/
theorem groupedPermutation_distSpec (E : CoPset) (encode : α → Val rT)
    (xs : List α) (sizes : List ℕ) (h : sizes.sum = xs.length) :
    IsDistSpec (GF := GF) E
      pl(&Occil.General.groupedPermutation &(listVal encode xs).fst
        &(listVal (fun n : ℕ => Val.int n) sizes).fst #())
      (law xs sizes) (listVal (listVal encode)) where
  spec F hF := by
    have hpartition (σ : Equiv.Perm (Fin xs.length)) :=
      twp_partition (rT := rT) (GF := GF) E encode sizes (Shuffle.output xs σ)
        (by simpa [Shuffle.output] using h)
    simp [partition, Exp.close, Exp.closeRec] at hpartition
    iintro Hcredit
    iterate 3 twp_pure
    twp_bind pl(&Occil.length &(listVal encode xs).fst)
    iapply tglWp_wand
    isplitl []
    · iapply twp_length E encode xs
    iintro %v %hv
    subst v
    twp_bind pl(&Occil.sumInts &(listVal (fun n : ℕ => Val.int n) sizes).fst)
    iapply tglWp_wand
    isplitl []
    · iapply WeightedChoice.twp_sumInts E sizes
    iintro %v %hv
    subst v
    rw [h]
    twp_pure
    rw [int_beq, beq_self_eq_true]
    twp_pure
    simp only [Shuffle.shuffle_openRec, Shuffle.shuffle_closeRec,
      ListPartition.splitAt_openRec, ListPartition.splitAt_closeRec]
    twp_bind pl(&Occil.shuffle &(listVal encode xs).fst)
    isimp only [← expectation xs sizes F hF] at Hcredit
    iapply (Shuffle.shuffle_distSpec E encode xs).wp
      (fun σ => F (groups sizes (Shuffle.output xs σ))) (measurable_of_countable _) _ $$ Hcredit
    iintro %σ Hcredit
    twp_pure
    twp_pure
    simp only [ListPartition.splitAt_openRec]
    iapply tglWp_wand
    isplitl []
    · iapply hpartition σ
    iintro %v %hv
    iexists groups sizes (Shuffle.output xs σ)
    iframe Hcredit
    ipureintro
    exact hv

end specification

end

end SampLib.GroupedPermutation
