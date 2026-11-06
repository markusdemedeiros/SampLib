import SampLib.Core.DistributionMapSupported
import SampLib.General.InverseCDF
import SampLib.General.LatinHypercube
import SampLib.General.PermutationTest
import SampLib.General.GroupedPermutation
import SampLib.General.PdfRejection

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

example {α : Type*} (E : CoPset) (input : α → Val rT) (xs : List α)
    (statistic : Val rT) (S : List α → ℤ)
    (hs : ∀ ys, ⊢ tglWp E pl(&statistic.fst &(listVal input ys).fst)
      (fun v : Val rT => iprop(⌜v = Val.int (S ys)⌝)))
    (n : ℕ) (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂PermutationTest.law xs S n) ∗ R -∗
      tglWp E pl(&Occil.General.permutationTest &(listVal input xs).fst
        &statistic.fst #int (n : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ,
          ⌜v = PermutationTest.encode n k⌝ ∗ ↯ (F k) ∗ R)) :=
  frame (PermutationTest.permutationTest_distSpec E input xs statistic S hs n)
    F (measurable_of_countable _) R

section grouped
variable {α : Type*}
local instance : MeasurableSpace (List (List α)) := ⊤

example (E : CoPset) (encode : α → Val rT) (xs : List α) (sizes : List ℕ)
    (h : sizes.sum = xs.length) (F : List (List α) → ℝ≥0∞)
    (hF : Measurable F) (R : IProp GF) :
    ⊢ ↯ (∫⁻ ys, F ys ∂GroupedPermutation.law xs sizes) ∗ R -∗
      tglWp E pl(&Occil.General.groupedPermutation &(listVal encode xs).fst
        &(listVal (fun n : ℕ => Val.int n) sizes).fst #())
        (fun v : Val rT => iprop(∃ ys : List (List α),
          ⌜v = listVal (listVal encode) ys⌝ ∗ ↯ (F ys) ∗ R)) :=
  frame (GroupedPermutation.groupedPermutation_distSpec E encode xs sizes h) F hF R

end grouped

example (E : CoPset) (D : PdfRejection.Model) (density : Val rT)
    (hd : ∀ x ∈ Set.Ico D.lower D.upper,
      ⊢ tglWp E pl(&density.fst #int x)
        (fun v : Val rT => iprop(⌜v = Val.int (D.height x : ℤ)⌝)))
    (hm : AcceptedProposal.mass (PdfRejection.proposal D) (PdfRejection.acceptance D) ≠ 0)
    (F : ℤ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂PdfRejection.law D hm) ∗ R -∗
      tglWp E pl(&Occil.General.pdfRejection &density.fst #int D.lower #int D.upper
        #int (D.envelope : ℤ) #())
        (fun v : Val rT => iprop(∃ x : ℤ, ⌜v = Val.int x⌝ ∗ ↯ (F x) ∗ R)) :=
  frame (PdfRejection.pdfRejection_distSpec E D density hd hm) F (measurable_of_countable _) R

example (E : CoPset) (a b : ℕ) (hb : 0 < b) (hab : a ≤ b)
    (F : Bool → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂RealCoin.law (IntegerThreshold.bias a b hb hab)) ∗ R -∗
      tglWp E pl(&Occil.uniformInt #int (b : ℤ) < #int (a : ℤ))
        (fun v : Val rT => iprop(∃ x : Bool, ⌜v = Val.bool x⌝ ∗ ↯ (F x) ∗ R)) :=
  frame (IntegerThreshold.threshold_distSpec E a b hb hab) F (measurable_of_countable _) R

example (E : CoPset) (scale count dimension : ℕ)
    (hc : 0 < count) (h : count ≤ scale) (hd : 0 < dimension)
    (F : List (List ℤ) → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ ys, F ys ∂LatinHypercube.law scale count hc h dimension) ∗ R -∗
      tglWp E pl(&Occil.General.latinHypercube #int (scale : ℤ) #int (count : ℤ)
        #int (dimension : ℤ) #())
        (fun v : Val rT => iprop(∃ ys : List (List ℤ),
          ⌜v = listVal (listVal Val.int) ys⌝ ∗ ↯ (F ys) ∗ R)) :=
  frame (LatinHypercube.latinHypercube_distSpec E scale count dimension hc h hd)
    F (measurable_of_countable _) R

example (E : CoPset) (D : FiniteCDF.Model) (oracle : Val rT)
    (ho : ∀ x ∈ Set.Icc D.lower D.upper,
      ⊢ tglWp E pl(&oracle.fst #int x)
        (fun v : Val rT => iprop(⌜v = Val.int (D.cdf x)⌝)))
    (F : ℤ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂FiniteCDF.law D) ∗ R -∗
      tglWp E pl(&Occil.General.inverseCDF #int (D.scale : ℤ) &oracle.fst
        #int D.lower #int D.upper #())
        (fun v : Val rT => iprop(∃ x : ℤ, ⌜v = Val.int x⌝ ∗ ↯ (F x) ∗ R)) :=
  frame (InverseCDF.inverseCDF_distSpec E D oracle ho) F (measurable_of_countable _) R

end integer_draws

example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {E : CoPset} {e : Exp rT} {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {encode : α → Val rT}
    (h : IsDistSpec (GF := GF) E e μ encode)
    (P : α → Prop) (hP : MeasurableSet {x | P x}) (hp : ∀ᵐ x ∂μ, P x)
    (f : α → β) (hf : Measurable f) (encode' : β → Val rT)
    (he : ∀ x, P x → encode x = encode' (f x))
    (F : β → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ ↯ (∫⁻ y, F y ∂μ.map f) ∗ R -∗ tglWp E e
      (fun v : Val rT => iprop(∃ y : β, ⌜v = encode' y⌝ ∗ ↯ (F y) ∗ R)) :=
  frame (h.map_supported P hP hp f hf encode' he) F hF R

example {E : CoPset} {e : Exp rT}
    (h : IsDistSpec (GF := GF) E e (MeasureTheory.Measure.dirac false) Val.bool) :
    IsDistSpec (GF := GF) E e (MeasureTheory.Measure.dirac (0 : ℕ))
      (fun _ => Val.bool false) := by
  have hm := h.map_supported (fun b => b = false) (measurableSet_singleton false)
    (by simp) (fun _ => (0 : ℕ)) measurable_const (fun _ => Val.bool false)
    (fun b hb => by subst b; rfl)
  simpa only [MeasureTheory.Measure.map_dirac] using hm

open MeasureTheory

example {α : Type*} (xs : List α) (c : ℤ) : PermutationTest.bias xs (fun _ => c) = 1 := by
  apply Subtype.ext
  have he : (PermutationTest.exceeds xs (fun _ => c)) ⁻¹' {true} = Set.univ := by
    ext σ
    simp [PermutationTest.exceeds]
  change (Shuffle.law xs).real ((PermutationTest.exceeds xs (fun _ => c)) ⁻¹' {true}) = 1
  rw [he]
  simp

example {α : Type*} (xs : List α) (S : List α → ℤ) (F : ℕ → ℝ≥0∞) :
    (∫⁻ k, F k ∂PermutationTest.law xs S 0) = F 0 := by simp [PermutationTest.law]

example : PermutationTest.encode (rT := rT) 0 0 = Val.pair (.int 1) (.int 1) := rfl

example {α : Type*} (xs : List α) (S : List α → ℤ) (n : ℕ) :
    (∫⁻ _ : ℕ, (∞ : ℝ≥0∞) ∂PermutationTest.law xs S n) = ∞ := by simp

section grouped_laws
local instance : MeasurableSpace (List (List ℕ)) := ⊤

example : GroupedPermutation.groups [0, 2, 0] ([7, 7] : List ℕ) = [[], [7, 7], []] := rfl

example : GroupedPermutation.law ([] : List ℕ) [0, 0] = Measure.dirac [[], []] := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [← GroupedPermutation.expectation _ _ F hF]
  change (∫⁻ σ, F (GroupedPermutation.groups [0, 0] (Shuffle.output [] σ))
    ∂Permutations.law 0) = _
  rw [Permutations.expectation_zero]
  simp [GroupedPermutation.groups, Shuffle.output]

example (xs : List ℕ) (sizes : List ℕ) :
    (∫⁻ _ : List (List ℕ), (∞ : ℝ≥0∞) ∂GroupedPermutation.law xs sizes) = ∞ := by simp

end grouped_laws

example (F : Bool → ℝ≥0∞) :
    (∫⁻ b, F b ∂RealCoin.law (IntegerThreshold.bias 0 5 (by decide) (by decide))) = F false := by
  simp [IntegerThreshold.bias, RationalCoin.bias, RealCoin.lintegral_law,
    RealCoin.credit, RealCoin.pmf]

example (F : Bool → ℝ≥0∞) :
    (∫⁻ b, F b ∂RealCoin.law (IntegerThreshold.bias 5 5 (by decide) (by decide))) = F true := by
  simp [IntegerThreshold.bias, RationalCoin.bias, RealCoin.lintegral_law,
    RealCoin.credit, RealCoin.pmf]

example (D : PdfRejection.Model)
    (hm : AcceptedProposal.mass (PdfRejection.proposal D) (PdfRejection.acceptance D) ≠ 0) :
    (∫⁻ _ : ℤ, (∞ : ℝ≥0∞) ∂PdfRejection.law D hm) = ∞ := by simp

example : LatinHypercube.rowsFrom [[2, 5], [7, 11]] 0 2 = [[2, 7], [5, 11]] := rfl

private theorem single_stratum :
    LatinHypercube1D.law 1 1 (by decide) (by decide) = Measure.dirac [0] := by
  apply Measure.ext_of_lintegral
  intro F _
  rw [← LatinHypercube1D.expectation]
  simp [Stratified1D.law, ListProduct.law, Stratified1D.coordinate,
    Stratified1D.boundary, RndIntExcRange.law, UniformInt.law,
    Measure.uniformOfFinset, Measure.dirac_prod_dirac, Measure.map_dirac,
    Shuffle.law, Shuffle.output, List.ofFn_succ]

example : LatinHypercube.law 1 1 (by decide) (by decide) 2 = Measure.dirac [[0, 0]] := by
  simp [LatinHypercube.law, single_stratum, SampleWithReplacement.law,
    Measure.dirac_prod_dirac, Measure.map_dirac, LatinHypercube.rowsFrom,
    LatinHypercube.row, List.ofFn_succ]

example (scale count dimension : ℕ) (hc : 0 < count) (h : count ≤ scale) :
    (∫⁻ _ : List (List ℤ), (∞ : ℝ≥0∞) ∂LatinHypercube.law scale count hc h dimension) = ∞ := by
  simp

private def thin : PdfRejection.Model where
  lower := -1
  upper := 1
  interval := by decide
  envelope := 1
  positive := by decide
  height x := if x = 0 then 1 else 0
  bounded x _ := by split_ifs <;> decide

private theorem thin_mass :
    AcceptedProposal.mass (PdfRejection.proposal thin) (PdfRejection.acceptance thin) =
      (2 : ℝ≥0∞)⁻¹ := by
  change (∫⁻ x, AcceptedProposal.weight (PdfRejection.acceptance thin) x
    ∂RndIntExcRange.law (-1) 1 (by decide)) = _
  rw [← RndIntExcRange.expectation, UniformInt.lintegral_law]
  norm_num [Finset.sum_range_succ, AcceptedProposal.weight, PdfRejection.acceptance, thin,
    IntegerThreshold.bias, RationalCoin.bias]

private theorem thin_positive :
    AcceptedProposal.mass (PdfRejection.proposal thin) (PdfRejection.acceptance thin) ≠ 0 := by
  rw [thin_mass]
  simp

example (F : ℤ → ℝ≥0∞) : (∫⁻ x, F x ∂PdfRejection.law thin thin_positive) = F 0 := by
  rw [PdfRejection.law, AcceptedProposal.law, lintegral_smul_measure, smul_eq_mul,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _)
      (measurable_of_countable _), thin_mass]
  change (2⁻¹ : ℝ≥0∞)⁻¹ * (∫⁻ x,
    AcceptedProposal.weight (PdfRejection.acceptance thin) x * F x
      ∂RndIntExcRange.law (-1) 1 (by decide)) = F 0
  rw [← RndIntExcRange.expectation, UniformInt.lintegral_law]
  norm_num [Finset.sum_range_succ, AcceptedProposal.weight, PdfRejection.acceptance, thin,
    IntegerThreshold.bias, RationalCoin.bias]
  rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv_cancel_left] <;> norm_num

private def certain : PdfRejection.Model where
  lower := -1
  upper := 1
  interval := by decide
  envelope := 1
  positive := by decide
  height _ := 1
  bounded _ _ := le_rfl

example : AcceptedProposal.mass (PdfRejection.proposal certain)
    (PdfRejection.acceptance certain) = 1 := by
  change (∫⁻ x, AcceptedProposal.weight (PdfRejection.acceptance certain) x
    ∂RndIntExcRange.law (-1) 1 (by decide)) = _
  rw [← RndIntExcRange.expectation, UniformInt.lintegral_law]
  norm_num [Finset.sum_range_succ, AcceptedProposal.weight, PdfRejection.acceptance, certain,
    IntegerThreshold.bias, RationalCoin.bias]
  rw [ENNReal.div_self] <;> norm_num

private def plateau : FiniteCDF.Model where
  lower := -2
  upper := 1
  nonempty := by decide
  scale := 4
  positive := by decide
  cdf x := if x < 0 then 1 else 4
  monotone := by
    intro a _ b _ hab
    change (if a < 0 then 1 else 4 : ℤ) ≤ (if b < 0 then 1 else 4)
    split_ifs <;> omega
  bounded x _ := by split_ifs <;> norm_num
  upper_mass := by norm_num

example : FiniteCDF.law plateau (Set.Iic (-2)) = 1 / 4 := by
  rw [FiniteCDF.cdf plateau (-2) (by norm_num [plateau])]
  norm_num [plateau, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]

example : FiniteCDF.law plateau (Set.Iic (-1)) = 1 / 4 := by
  rw [FiniteCDF.cdf plateau (-1) (by norm_num [plateau])]
  norm_num [plateau, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]

private def singletonCDF : FiniteCDF.Model where
  lower := -7
  upper := -7
  nonempty := le_rfl
  scale := 1
  positive := by decide
  cdf _ := 1
  monotone := fun _ _ _ _ _ => le_rfl
  bounded _ _ := by norm_num
  upper_mass := rfl

private theorem singleton_quantile (i : Fin singletonCDF.scale) :
    FiniteCDF.quantile singletonCDF i = -7 := by
  have hi := (FiniteCDF.quantile_mem singletonCDF i).1
  change -7 ≤ _ ∧ _ ≤ -7 at hi
  omega

example : FiniteCDF.law singletonCDF = Measure.dirac (-7) := by
  apply Measure.ext_of_lintegral
  intro F _
  rw [← FiniteCDF.expectation]
  simp only [singleton_quantile]
  simp [singletonCDF]

example (D : FiniteCDF.Model) :
    (∫⁻ _ : ℤ, (∞ : ℝ≥0∞) ∂FiniteCDF.law D) = ∞ := by simp

end
end ReviewExpansionStructured

#print axioms SampLib.PermutationTest.permutationTest_distSpec
#print axioms SampLib.PermutationTest.expectation
#print axioms SampLib.GroupedPermutation.groupedPermutation_distSpec
#print axioms SampLib.ListPartition.twp_splitAt
#print axioms SampLib.BooleanEvent.map_eq
#print axioms SampLib.PdfRejection.pdfRejection_distSpec
#print axioms SampLib.IntegerThreshold.threshold_distSpec
#print axioms SampLib.RndIntExcRange.ae_mem
#print axioms SampLib.AcceptedProposal.expectation_preservation

#print axioms SampLib.LatinHypercube.latinHypercube_distSpec
#print axioms SampLib.LatinHypercube.columns_valid
#print axioms SampLib.SampleWithReplacement.all_ae
#print axioms SampLib.ListProduct.length_ae

#print axioms SampLib.InverseCDF.inverseCDF_distSpec
#print axioms SampLib.FiniteCDF.cdf
#print axioms SampLib.IsDistSpec.map_supported
