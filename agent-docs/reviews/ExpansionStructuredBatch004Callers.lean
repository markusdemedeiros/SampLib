import SampLib.Combinatorial.Shuffle
import SampLib.Combinatorial.PositiveComposition
import SampLib.Combinatorial.WeakComposition
import SampLib.General.LatinHypercube1D
import SampLib.General.StratifiedBox
import SampLib.General.ClassifiedModel

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

section integer_draws
variable [ProbLangDist.IsUniformInt rT]

example {α : Type*} (E : CoPset) (encode : α → Val rT) (xs : List α)
    (F : Equiv.Perm (Fin xs.length) → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ σ, F σ ∂Shuffle.law xs) ∗ R -∗
      tglWp E pl(&Occil.shuffle &(listVal encode xs).fst)
        (fun v : Val rT => iprop(∃ σ : Equiv.Perm (Fin xs.length),
          ⌜v = listVal encode (Shuffle.output xs σ)⌝ ∗ ↯ (F σ) ∗ R)) :=
  frame (Shuffle.shuffle_distSpec E encode xs) F (measurable_of_countable _) R

section composition_callers
local instance : MeasurableSpace (List ℤ) := ⊤

example (E : CoPset) (n total : ℕ) (hn : 0 < n) (ht : n ≤ total)
    (F : List ℤ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ xs, F xs ∂Compositions.law n total hn ht) ∗ R -∗
      tglWp E pl(&Occil.positiveComposition #int (n : ℤ) #int (total : ℤ))
        (fun v : Val rT => iprop(∃ xs : List ℤ,
          ⌜v = listVal Val.int xs⌝ ∗ ↯ (F xs) ∗ R)) :=
  frame (PositiveComposition.positiveComposition_distSpec E n total hn ht)
    F (measurable_of_countable _) R

example (E : CoPset) (n total : ℕ) (hn : 0 < n)
    (F : List ℤ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ xs, F xs ∂Compositions.weakLaw n total hn) ∗ R -∗
      tglWp E pl(&Occil.weakComposition #int (n : ℤ) #int (total : ℤ))
        (fun v : Val rT => iprop(∃ xs : List ℤ,
          ⌜v = listVal Val.int xs⌝ ∗ ↯ (F xs) ∗ R)) :=
  frame (WeakComposition.weakComposition_distSpec E n total hn)
    F (measurable_of_countable _) R

end composition_callers

example (E : CoPset) (scale strata : ℕ) (hs : 0 < strata) (h : strata ≤ scale)
    (F : List ℤ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ xs, F xs ∂LatinHypercube1D.law scale strata hs h) ∗ R -∗
      tglWp E pl(&Occil.General.latinHypercube1D
        #int (scale : ℤ) #int (strata : ℤ) #())
        (fun v : Val rT => iprop(∃ xs : List ℤ,
          ⌜v = listVal Val.int xs⌝ ∗ ↯ (F xs) ∗ R)) :=
  frame (LatinHypercube1D.latinHypercube1D_distSpec E scale strata hs h)
    F (measurable_of_countable _) R

example (E : CoPset) (scale bins dimension perCell : ℕ)
    (hb : 0 < bins) (h : bins ≤ scale) (hd : 0 < dimension)
    (F : List (List ℤ) → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ xs, F xs ∂StratifiedBox.law scale bins hb h dimension perCell) ∗ R -∗
      tglWp E pl(&Occil.General.stratifiedBox #int (scale : ℤ) #int (bins : ℤ)
        #int (dimension : ℤ) #int (perCell : ℤ) #())
        (fun v : Val rT => iprop(∃ xs : List (List ℤ),
          ⌜v = listVal (listVal Val.int) xs⌝ ∗ ↯ (F xs) ∗ R)) :=
  frame (StratifiedBox.stratifiedBox_distSpec E scale bins dimension perCell hb h hd)
    F (measurable_of_countable _) R

example {α : Type*} [MeasurableSpace α] (E : CoPset)
    (weights : List ℕ) [NeZero weights.sum]
    (μ : Fin weights.length → MeasureTheory.Measure α)
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)] (output : α → Val rT)
    (models : Fin weights.length → Val rT)
    (hm : ∀ i, IsDistSpec (GF := GF) E pl(&(models i).fst #()) (μ i) output)
    (F : Fin weights.length × α → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂ClassifiedModel.law weights μ) ∗ R -∗
      tglWp E pl(&Occil.General.classifiedModel
        &(listVal (fun w : ℕ => Val.int (w : ℤ)) weights).fst
        &(listVal id (List.ofFn models)).fst #())
        (fun v : Val rT => iprop(∃ x : Fin weights.length × α,
          ⌜v = ClassifiedModel.encode output x⌝ ∗ ↯ (F x) ∗ R)) :=
  frame (ClassifiedModel.classifiedModel_distSpec E weights μ output models hm) F hF R

end integer_draws

open MeasureTheory

example (σ : Equiv.Perm (Fin 2)) : Shuffle.output ([9, 9] : List ℤ) σ = [9, 9] := by
  have h (i : Fin 2) : ([9, 9] : List ℤ).get i = 9 := by fin_cases i <;> rfl
  unfold Shuffle.output
  rw [show (([9, 9] : List ℤ).get ∘ σ) = (fun _ => 9) from funext (fun i => h (σ i))]
  rfl

example (σ : Equiv.Perm (Fin 0)) : Shuffle.output ([] : List ℤ) σ = [] := rfl

example (n total : ℕ) (hn : 0 < n) (ht : n ≤ total) :
    (∫⁻ _ : List ℤ, (∞ : ℝ≥0∞) ∂Compositions.law n total hn ht) = ∞ := by simp

example (n total : ℕ) (hn : 0 < n) :
    (∫⁻ _ : List ℤ, (∞ : ℝ≥0∞) ∂Compositions.weakLaw n total hn) = ∞ := by simp

example : Compositions.law 3 5 (by decide) (by decide) {[1, 3, 1]} = 1 / 6 := by
  norm_num [Compositions.law_singleton, Compositions.positive, Nat.choose]

example : Compositions.law 3 5 (by decide) (by decide) {[1, 0, 4]} = 0 := by
  norm_num [Compositions.law_singleton, Compositions.positive]

example (total : ℕ) (h : 0 < total) :
    Compositions.law 1 total (by decide) h {[(total : ℤ)]} = 1 := by
  simp [Compositions.law_singleton, Compositions.positive, Nat.ne_of_gt h]

example : Compositions.weakLaw 3 0 (by decide) {[0, 0, 0]} = 1 := by
  norm_num [Compositions.weakLaw_singleton, Compositions.weak]

example : Compositions.weakLaw 3 2 (by decide) {[0, 2, 0]} = 1 / 6 := by
  norm_num [Compositions.weakLaw_singleton, Compositions.weak, Nat.choose]

example (scale strata : ℕ) (hs : 0 < strata) (h : strata ≤ scale) :
    (∫⁻ _ : List ℤ, (∞ : ℝ≥0∞) ∂LatinHypercube1D.law scale strata hs h) = ∞ := by simp

example (scale bins : ℕ) (hb : 0 < bins) (h : bins ≤ scale) (d k : ℕ) :
    (∫⁻ _ : List (List ℤ), (∞ : ℝ≥0∞) ∂StratifiedBox.law scale bins hb h d k) = ∞ := by
  simp

example (scale bins : ℕ) (hb : 0 < bins) (h : bins ≤ scale) (d cell : ℕ) :
    StratifiedBox.chunkLaw scale bins hb h d 0 cell = Measure.dirac [] := by
  simp [StratifiedBox.chunkLaw, SampleWithReplacement.law,
    Measure.map_dirac' (measurable_of_countable _)]

example (scale bins : ℕ) (hb : 0 < bins) (h : bins ≤ scale) (d cell n : ℕ) :
    StratifiedBox.lawFrom scale bins hb h d 0 cell n = Measure.dirac [] := by
  induction n generalizing cell with
  | zero => simp [StratifiedBox.lawFrom, ListProduct.law,
      Measure.map_dirac' (measurable_of_countable _)]
  | succ n ih =>
    apply Measure.ext_of_lintegral
    intro F hF
    rw [← StratifiedBox.expectation]
    simp only [ih]
    rw [MeasureTheory.lintegral_dirac]
    simp [StratifiedBox.chunkLaw, SampleWithReplacement.law,
      Measure.map_dirac' (measurable_of_countable _)]

private instance : NeZero ([0, 3] : List ℕ).sum := ⟨by decide⟩

example (F : Fin ([0, 3] : List ℕ).length × ℤ → ℝ≥0∞) :
    (∫⁻ p, F p ∂ClassifiedModel.law [0, 3]
      (fun i => Measure.dirac (if i.val = 0 then (-10 : ℤ) else 20))) = F (1, 20) := by
  rw [ClassifiedModel.law, Measure.lintegral_bind
    (measurable_of_countable _).aemeasurable (measurable_of_countable F).aemeasurable,
    WeightedChoice.lintegral_law]
  norm_num [WeightedChoice.weightedSum, ClassifiedModel.position, Choice.position,
    MeasureTheory.lintegral_map, Measure.map_dirac]
  rw [mul_comm (3 : ℝ≥0∞), ENNReal.mul_div_cancel_right] <;> norm_num


example (F : List ℤ → ℝ≥0∞) :
    (∫⁻ xs, F xs ∂LatinHypercube1D.law 1 1 (by decide) (by decide)) = F [0] := by
  rw [← LatinHypercube1D.expectation]
  simp [Stratified1D.law, ListProduct.law, Stratified1D.coordinate,
    Stratified1D.boundary, RndIntExcRange.law, UniformInt.law,
    Measure.uniformOfFinset, Measure.dirac_prod_dirac, Measure.map_dirac,
    Shuffle.law, Shuffle.output, List.ofFn_succ]

example (F : Fin ([0, 3] : List ℕ).length × ℤ → ℝ≥0∞) :
    (∫⁻ p, (if p.1.val = 0 then ∞ else F p : ℝ≥0∞) ∂ClassifiedModel.law [0, 3]
      (fun i => Measure.dirac (if i.val = 0 then (-10 : ℤ) else 20))) = F (1, 20) := by
  rw [ClassifiedModel.law, Measure.lintegral_bind
    (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable,
    WeightedChoice.lintegral_law]
  norm_num [WeightedChoice.weightedSum, ClassifiedModel.position, Choice.position,
    MeasureTheory.lintegral_map, Measure.map_dirac]
  rw [mul_comm (3 : ℝ≥0∞), ENNReal.mul_div_cancel_right] <;> norm_num

end
end ReviewExpansionStructured

#print axioms SampLib.Shuffle.shuffle_distSpec

#print axioms SampLib.PositiveComposition.positiveComposition_distSpec

#print axioms SampLib.WeakComposition.weakComposition_distSpec

#print axioms SampLib.LatinHypercube1D.latinHypercube1D_distSpec

#print axioms SampLib.StratifiedBox.stratifiedBox_distSpec

#print axioms SampLib.ClassifiedModel.classifiedModel_distSpec



#print axioms SampLib.ArrayPermutation.owns_after_swap
#print axioms SampLib.ArrayPermutation.owns_after_shuffle
#print axioms SampLib.Compositions.law_eq_uniform
#print axioms SampLib.Compositions.weakLaw_singleton
#print axioms SampLib.StratifiedBox.expectation
#print axioms SampLib.ClassifiedModel.expectation
