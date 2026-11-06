import SampLib.Discrete.FisherMultivariate
import SampLib.Weighted.TwoLevelChoice
import SampLib.Common.Laws.BitRecycler
import SampLib.Weighted.FYKY
import Metrology.Iris.LocalBI

/-! Independent signed rejection, conditioned urn and block-categorical clients. -/

open Set ProbLang
open scoped ENNReal NNReal

namespace ExpansionDiscreteAudit

noncomputable section

section mathematics

open MeasureTheory Measure SampLib

example : WeightedBlocks.chunks 2 [0, 0, 2, 0, 3] = [[0, 0], [2, 0], [3]] := by
  norm_num [WeightedBlocks.chunks_cons, WeightedBlocks.chunks_nil]
example : WeightedBlocks.totals (WeightedBlocks.chunks 2 [0, 0, 2, 0, 3]) = [0, 2, 3] :=
  by norm_num [WeightedBlocks.chunks_cons, WeightedBlocks.chunks_nil, WeightedBlocks.totals]
example : WeightedBlocks.chunks 9 [0, 2, 0, 3] = [[0, 2, 0, 3]] := by
  norm_num [WeightedBlocks.chunks_cons, WeightedBlocks.chunks_nil]
example : WeightedBlocks.chunks 1 [0, 2, 0, 3] = [[0], [2], [0], [3]] := by
  norm_num [WeightedBlocks.chunks_cons, WeightedBlocks.chunks_nil]

example (F : ℕ → ℝ≥0∞) :
    ∫⁻ i, WeightedBlocks.continuation 2 (WeightedBlocks.chunks 2 [0, 0, 2, 0, 3]) F i
      ∂WeightedChoice.law [0, 2, 3] = ∫⁻ i, F i ∂WeightedChoice.law [0, 0, 2, 0, 3] := by
  simpa only [WeightedBlocks.chunks_cons, WeightedBlocks.chunks_nil, WeightedBlocks.totals,
    List.take_succ_cons, List.take_zero, List.take_nil, List.drop_succ_cons, List.drop_zero,
    List.drop_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    zero_add] using WeightedBlocks.expectation 2 [0, 0, 2, 0, 3] F

example : (∫⁻ i, (if i = 2 then 1 else if i = 4 then 2 else ∞ : ℝ≥0∞)
    ∂WeightedChoice.law [0, 0, 2, 0, 3]) = (8 : ℝ≥0∞) / 5 := by
  rw [WeightedChoice.lintegral_law]
  norm_num [WeightedChoice.weightedSum]

example : (∫⁻ _i, (∞ : ℝ≥0∞) ∂WeightedChoice.law [0, 0, 2, 0, 3]) = ∞ := by
  let : NeZero ([0, 0, 2, 0, 3] : List ℕ).sum := ⟨by decide⟩
  simp

example : BitRecycler.credit .lower 3 (fun _ => 0) 2 1 0 = (1 : ℝ≥0∞) / 4 := by
  norm_num [BitRecycler.credit, BitRecycler.kernel, Finset.sum_range_succ]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

example : BitRecycler.credit .upper 3 (fun _ => 0) 2 1 0 = (1 : ℝ≥0∞) / 4 := by
  norm_num [BitRecycler.credit, BitRecycler.kernel, Finset.sum_range_succ]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

example : BitRecycler.credit .lower 5 (fun _ => 0) 3 1 0 = (3 : ℝ≥0∞) / 8 := by
  norm_num [BitRecycler.credit, BitRecycler.kernel, Finset.sum_range_succ]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num

example : BitRecycler.credit .upper 5 (fun _ => 0) 3 1 0 = (3 : ℝ≥0∞) / 8 := by
  norm_num [BitRecycler.credit, BitRecycler.kernel, Finset.sum_range_succ]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num

example : BitRecycler.credit .lower 3 (fun k => if k = 1 then ∞ else 0) 1 2 0 = ∞ := by
  norm_num [BitRecycler.credit, BitRecycler.kernel, Finset.sum_range_succ]
  exact ENNReal.top_div_of_ne_top (by finiteness)

example : BitRecycler.credit .upper 3 (fun k => if k = 1 then ∞ else 0) 1 2 0 =
    (1 : ℝ≥0∞) / 2 := by
  norm_num [BitRecycler.credit, BitRecycler.kernel, Finset.sum_range_succ]

example (o : BitRecycler.Orientation) (F : ℕ → ℝ≥0∞) :
    BitRecycler.credit o 5 F 3 1 0 ≤ (∫⁻ j, F j ∂UniformInt.law 5) + (4 : ℝ≥0∞) / 8 := by
  convert BitRecycler.initial_bound o 5 (by decide) (by decide) 3 F using 1
  norm_num

example (o : BitRecycler.Orientation) (F : ℕ → ℝ≥0∞) :
    ∑ c ∈ Finset.range 3, BitRecycler.credit o 5 F 3 3 c ≤
      3 * BitRecycler.outputCredit 5 F + (4 : ℝ≥0∞) / 8 := by
  convert BitRecycler.sum_credit_le o 5 (by decide) 3 3 (by decide) F using 1
  norm_num

example (ε : ℝ≥0∞) (hε : 0 < ε) : ∃ T : ℕ, (2 : ℝ≥0∞) / 2 ^ T ≤ ε := by
  simpa using BitRecycler.exists_horizon 3 (by decide) ε hε

#print axioms SampLib.BitRecycler.kernel_sum
#print axioms SampLib.BitRecycler.sum_credit_le
#print axioms SampLib.BitRecycler.initial_bound
#print axioms SampLib.BitRecycler.exists_horizon

end mathematics

local instance : NeZero ([0, 0, 2, 0, 3] : List ℕ).sum := ⟨by decide⟩
local instance : NeZero ([0, 2, 0, 3] : List ℕ).sum := ⟨by decide⟩

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem frame {α : Type} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {E : CoPset} {e : Exp rT}
    {encode : α → Val rT} (h : IsDistSpec (GF := GF) E e μ encode)
    (F : α → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂μ) ∗ I -∗ tglWp E e
      (fun v : Val rT => iprop(∃ x : α, ⌜v = encode x⌝ ∗ ↯ (F x) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply (h.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %x Hcredit
  iexists x
  iframe Hcredit HI
  itrivial

example (E : CoPset) (n : ℕ) (counts odds : List ℕ) (hlen : counts.length = odds.length)
    (hodds : ∀ o ∈ odds, 0 < o) (hn : n ≤ counts.sum)
    (F : List ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ xs, F xs ∂FisherMultivariate.law n counts odds hlen hodds hn) ∗ I -∗
      tglWp E pl(&Occil.DiscreteExtra.fisherMultivariate #int (n : ℤ)
        &(NatCounters.encode counts).fst &(NatCounters.encode odds).fst)
        (fun v : Val rT => iprop(∃ xs : List ℕ,
          ⌜v = NatCounters.encode xs⌝ ∗ ↯ (F xs) ∗ I)) :=
  frame (FisherMultivariate.fisherMultivariate_distSpec E n counts odds hlen hodds hn) F I

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.DiscreteExtra.fisherMultivariate #0
      &(NatCounters.encode []).fst &(NatCounters.encode []).fst)
    (MeasureTheory.Measure.dirac ([] : List ℕ)) NatCounters.encode := by
  have h := FisherMultivariate.fisherMultivariate_distSpec (rT := rT) (GF := GF)
    E 0 [] [] rfl (by simp) (by decide)
  have he : FisherMultivariate.law 0 [] [] rfl (by simp) (by decide) =
      MeasureTheory.Measure.dirac ([] : List ℕ) := by
    simpa using FisherMultivariate.law_zero [] [] rfl (by simp)
  constructor
  intro F hF
  simpa only [he, Nat.cast_zero] using h.spec F hF

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.DiscreteExtra.fisherMultivariate #3
      &(NatCounters.encode [0, 2, 1]).fst &(NatCounters.encode [5, 1, 3]).fst)
    (MeasureTheory.Measure.dirac ([0, 2, 1] : List ℕ)) NatCounters.encode := by
  have h := FisherMultivariate.fisherMultivariate_distSpec (GF := GF) E
    3 [0, 2, 1] [5, 1, 3] rfl (by simp) (by decide)
  have he := FisherMultivariate.law_full [0, 2, 1] [5, 1, 3] rfl (by simp)
  norm_num only [List.sum_cons, List.sum_nil, add_zero, zero_add] at he
  simpa only [he, Nat.cast_ofNat] using h

#print axioms SampLib.FisherMultivariate.fisherMultivariate_distSpec

example (E : CoPset) (ws : List ℕ) (size : ℕ) [NeZero ws.sum] [NeZero size]
    (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) ∗ I -∗
      tglWp E pl(&Occil.WeightedVariants.twoLevelChoice
        &(listVal (fun n : ℕ => Val.int n) ws).fst #int (size : ℤ) #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ ↯ (F i) ∗ I)) :=
  frame (TwoLevelChoice.twoLevelChoice_distSpec E ws size) F I

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.WeightedVariants.twoLevelChoice
      &(listVal (fun n : ℕ => Val.int n) [0, 0, 2, 0, 3]).fst #2 #())
    (WeightedChoice.law [0, 0, 2, 0, 3]) (fun i : ℕ => Val.int (i : ℤ)) :=
  TwoLevelChoice.twoLevelChoice_distSpec E [0, 0, 2, 0, 3] 2

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.WeightedVariants.twoLevelChoice
      &(listVal (fun n : ℕ => Val.int n) [0, 2, 0, 3]).fst #9 #())
    (WeightedChoice.law [0, 2, 0, 3]) (fun i : ℕ => Val.int (i : ℤ)) :=
  TwoLevelChoice.twoLevelChoice_distSpec E [0, 2, 0, 3] 9

#print axioms SampLib.TwoLevelChoice.twoLevelChoice_distSpec
#print axioms SampLib.WeightedBlocks.expectation
#print axioms SampLib.WeightedBlocks.conditional_blocks


example (E : CoPset) (n : ℕ) [NeZero n] (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ j, F j ∂UniformInt.law n) ∗ I -∗
      tglWp E pl(&Occil.Weighted.fyky #int (n : ℤ))
        (fun result : Val rT => iprop(∃ j : ℕ,
          ⌜result = Val.int (j : ℤ)⌝ ∗ ↯ (F j) ∗ I)) :=
  frame (FYKY.fyky_distSpec E n) F I

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ j, F j ∂UniformInt.law 1) ∗ I -∗
      tglWp E pl(&Occil.Weighted.fyky #1)
        (fun result : Val rT => iprop(∃ j : ℕ,
          ⌜result = Val.int (j : ℤ)⌝ ∗ ↯ (F j) ∗ I)) :=
  frame (FYKY.fyky_one_distSpec E) F I

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.Weighted.fyky #3) (UniformInt.law 3) (fun j : ℕ => Val.int (j : ℤ)) :=
  FYKY.fyky_distSpec E 3

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.Weighted.fyky #5) (UniformInt.law 5) (fun j : ℕ => Val.int (j : ℤ)) :=
  FYKY.fyky_distSpec E 5

#print axioms SampLib.FYKY.fyky_distSpec
#print axioms SampLib.FYKY.fyky_one_distSpec

end

end ExpansionDiscreteAudit
