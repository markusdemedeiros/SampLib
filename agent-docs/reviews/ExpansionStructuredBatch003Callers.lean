import SampLib.Templates
import SampLib.Core.ListEncoding
import SampLib.Core.DistributionMap
import SampLib.Continuous.Gaussian
import SampLib.Continuous.OrderStatistic
import SampLib.General.Bootstrap
import SampLib.General.Histogram
import SampLib.Core.Laws.Permutations
import SampLib.Core.ArrayOwnership

open ProbLang
open scoped ENNReal

namespace ReviewExpansionStructured

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- A caller retains its own resource while spending the expected sampler credit. -/
theorem frame {α : Type _} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {E : CoPset} {e : Exp rT}
    {encode : α → Val rT} (h : IsDistSpec (GF := GF) E e μ encode)
    (F : α → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂μ) ∗ R -∗ tglWp E e
      (fun v : Val rT => iprop(∃ x : α, ⌜v = encode x⌝ ∗ ↯ (F x) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply (h.wp F hF _) $$ Hcredit
  iintro %x Hcredit
  iexists x
  iframe Hcredit HR
  itrivial


example {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    {E : CoPset} {e : Exp rT} {encode : α → Val rT}
    (h : IsDistSpec (GF := GF) E e μ encode) (f : α → β) (hf : Measurable f)
    (encode' : β → Val rT) (he : ∀ x, encode x = encode' (f x))
    (F : β → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ ↯ (∫⁻ y, F y ∂μ.map f) ∗ R -∗ tglWp E e
      (fun v : Val rT => iprop(∃ y : β, ⌜v = encode' y⌝ ∗ ↯ (F y) ∗ R)) :=
  frame (h.map f hf encode' he) F hF R

example {α : Type _} [ProbLangDist.IsUniformInt rT] (E : CoPset)
    (encode : α → Val rT) (xs : List α) [NeZero xs.length] (replicates : ℕ)
    (F : (Fin replicates → Fin xs.length → Fin xs.length) → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ ys, F ys ∂Bootstrap.law xs.length replicates) ∗ R -∗
      tglWp E pl(&Occil.General.bootstrap &(listVal encode xs).fst
        #int (replicates : ℤ) #())
        (fun v : Val rT => iprop(∃ ys : Fin replicates → Fin xs.length → Fin xs.length,
          ⌜v = listVal (fun zs => listVal (fun i => encode (xs.get i))
            (List.ofFn zs)) (List.ofFn ys)⌝ ∗ ↯ (F ys) ∗ R)) :=
  frame (Bootstrap.bootstrap_distSpec E encode xs replicates)
    F (measurable_of_countable _) R

example {α : Type _} (E : CoPset) (encode : α → Val rT) (replicates : ℕ)
    (F : (Fin replicates → Unit) → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ ys, F ys ∂SampleWithReplacement.law
      (MeasureTheory.Measure.dirac ()) replicates) ∗ R -∗
      tglWp E pl(&Occil.General.bootstrap &(listVal encode []).fst
        #int (replicates : ℤ) #())
        (fun v : Val rT => iprop(∃ ys : Fin replicates → Unit,
          ⌜v = listVal (fun _ : Unit => listVal encode []) (List.ofFn ys)⌝ ∗
            ↯ (F ys) ∗ R)) :=
  frame (Bootstrap.bootstrap_empty_distSpec E encode replicates)
    F (measurable_of_countable _) R

example (n : ℕ) [NeZero n] :
    (∫⁻ _ : Fin 0 → Fin n → Fin n, (7 : ℝ≥0∞) ∂Bootstrap.law n 0) = 7 := by simp

example (n : ℕ) [NeZero n] (r : ℕ) :
    (∫⁻ _ : Fin r → Fin n → Fin n, (∞ : ℝ≥0∞) ∂Bootstrap.law n r) = ∞ := by simp

example [ProbLangDist.IsUniformInt rT] (E : CoPset) (points : List ℤ)
    (weights : List ℕ) [NeZero weights.sum]
    (hlen : points.length = weights.length + 1)
    (hw : ∀ i, i < weights.length → points[i]?.getD 0 < points[i + 1]?.getD 0)
    (F : ℤ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂Histogram.law points weights hw) ∗ R -∗
      tglWp E pl(&Occil.General.histogram &(listVal (fun z : ℤ => Val.int z) points).fst
        &(listVal (fun w : ℕ => Val.int (w : ℤ)) weights).fst #())
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z) ∗ R)) :=
  frame (Histogram.histogram_distSpec E points weights hlen hw)
    F (measurable_of_countable _) R

private theorem hist_width (i : ℕ) (hi : i < 2) :
    ([0, 1, 4] : List ℤ)[i]?.getD 0 < ([0, 1, 4] : List ℤ)[i + 1]?.getD 0 := by
  have h : i = 0 ∨ i = 1 := by omega
  rcases h with rfl | rfl <;> norm_num

private instance : NeZero ([1, 1] : List ℕ).sum := ⟨by decide⟩
private instance : NeZero ([0, 1] : List ℕ).sum := ⟨by decide⟩

example : (∫⁻ z, (if z = 0 then 1 else 0 : ℝ≥0∞)
    ∂Histogram.law [0, 1, 4] [1, 1] hist_width) = 1 / 2 := by
  rw [← Histogram.expectation]
  norm_num [WeightedChoice.lintegral_law, WeightedChoice.weightedSum, Histogram.binLaw,
    RndIntExcRange.law, MeasureTheory.lintegral_map (measurable_of_countable _)
      (measurable_of_countable _), UniformInt.lintegral_law, Finset.sum_range_succ]

  have hne (x : ℕ) : (1 : ℤ) + (x : ℤ) ≠ 0 := by omega
  simp [hne, one_div]

example : (∫⁻ z, (if z = 0 then ∞ else 7 : ℝ≥0∞)
    ∂Histogram.law [0, 1, 4] [0, 1] hist_width) = 7 := by
  rw [← Histogram.expectation]
  norm_num [WeightedChoice.lintegral_law, WeightedChoice.weightedSum, Histogram.binLaw,
    RndIntExcRange.law, MeasureTheory.lintegral_map (measurable_of_countable _)
      (measurable_of_countable _), UniformInt.lintegral_law, Finset.sum_range_succ]
  rw [show (21 : ℝ≥0∞) = 7 * 3 by norm_num, ENNReal.mul_div_cancel_right] <;> norm_num

example (n : ℕ) : (∫⁻ _ : Equiv.Perm (Fin n), (∞ : ℝ≥0∞) ∂Permutations.law n) = ∞ := by
  simp

example (F : Equiv.Perm (Fin 0) → ℝ≥0∞) :
    (∫⁻ σ, F σ ∂Permutations.law 0) = F (Equiv.refl _) := Permutations.expectation_zero F

example (F : Equiv.Perm (Fin 1) → ℝ≥0∞) :
    (∫⁻ σ, F σ ∂Permutations.law 1) = F (Equiv.refl _) := Permutations.expectation_one F

example {α : Type _} {n : ℕ} (a : Fin n → α) (i : Fin n) :
    ((List.ofFn a).set i (a i)).set i (a i) = List.ofFn a := by
  simpa using Permutations.ofFn_swap a i i

example [ProbLangDist.IsUniformInt rT] (E : CoPset) (l : Loc)
    (vs : List (Val rT)) (i : Fin vs.length) (R : IProp GF) :
    ⊢ Array.owns l vs ∗ R -∗
      tglWp E pl(!(#loc l +ₗ #int (i.val : ℤ)))
        (fun v => iprop(⌜v = vs.get i⌝ ∗ Array.owns l vs ∗ R)) := by
  iintro ⟨Ha, HR⟩
  iapply tglWp_wand
  isplitl [Ha]
  · iapply Array.twp_load_index E l vs i $$ Ha
  iintro %v ⟨%hv, Ha⟩
  iframe %hv Ha HR

#print axioms IsDistSpec.map
#print axioms Bootstrap.bootstrap_distSpec
#print axioms Bootstrap.bootstrap_empty_distSpec
#print axioms Histogram.histogram_distSpec
#print axioms Histogram.expectation
#print axioms Permutations.expectation
#print axioms Permutations.ofFn_swap
#print axioms Array.twp_readArray
#print axioms Array.twp_load_ofFn
#print axioms Array.twp_store_ofFn

section real_model

variable [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
  [ErisGS ℝ hlc GF]

example [ProbLangDist.IsUniformInt ℝ] (E : CoPset) (F : ℝ → ℝ≥0∞)
    (hF : Measurable F) (R : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂Gaussian.law) ∗ R -∗ tglWp E pl(&Occil.gaussian #())
      (fun v : Val ℝ => iprop(∃ z : ℝ, ⌜v = Val.real z⌝ ∗ ↯ (F z) ∗ R)) :=
  frame (rT := ℝ) (Gaussian.gaussian_distSpec E) F hF R

example : Gaussian.law = ProbabilityTheory.gaussianReal 0 1 := rfl

example : (∫⁻ _ : ℝ, (∞ : ℝ≥0∞) ∂Gaussian.law) = ∞ := by simp

example (E : CoPset) (n k : ℕ) (hk : 0 < k ∧ k ≤ n)
    (F : OrderStatistic.Sample n → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ ↯ (∫⁻ s, F s ∂OrderStatistic.law n) ∗ R -∗
      tglWp E pl(&Occil.orderStatistic #int (n : ℤ) #int (k : ℤ))
        (fun v : Val ℝ => iprop(∃ s : OrderStatistic.Sample n,
          ⌜v = Val.real (OrderStatistic.selected n k hk s)⌝ ∗ ↯ (F s) ∗ R)) :=
  frame (rT := ℝ) (OrderStatistic.orderStatistic_distSpec E n k hk) F hF R

example (x : ℝ) : OrderStatistic.selected 1 1 (by norm_num) (x, ()) = x := rfl

example : OrderStatistic.selected 3 2 (by norm_num) (2, 1, 1, ()) = 1 := by
  norm_num [OrderStatistic.selected, OrderStatistic.sorted, OrderStatistic.samples,
    List.insertionSort, List.orderedInsert]

example : OrderStatistic.selected 3 3 (by norm_num) (2, 1, 1, ()) = 2 := by
  norm_num [OrderStatistic.selected, OrderStatistic.sorted, OrderStatistic.samples,
    List.insertionSort, List.orderedInsert]

example (n : ℕ) : (∫⁻ _ : OrderStatistic.Sample n, (∞ : ℝ≥0∞)
    ∂OrderStatistic.law n) = ∞ := by simp

#print axioms Gaussian.gaussian_distSpec
#print axioms Gaussian.expectation
#print axioms OrderStatistic.orderStatistic_distSpec
#print axioms OrderStatistic.sorted_unique
#print axioms OrderStatistic.expectation

end real_model

end

end ReviewExpansionStructured
