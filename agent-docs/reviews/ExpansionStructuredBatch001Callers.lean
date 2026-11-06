import SampLib.Templates
import SampLib.SupportedSpec
import SampLib.ListEncoding
import SampLib.Samplers.GenerativeModel
import SampLib.Samplers.InverseQuantile
import SampLib.Samplers.RealCoin
import SampLib.Samplers.KernelDensity
import SampLib.Samplers.UniformBoxPoint
import SampLib.Samplers.FlipBits

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
    (E : CoPset) (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (latent decoder : Val rT) (encode : α → Val rT) (encode' : β → Val rT)
    (decode : α → β) (hdecode : Measurable decode)
    (hlatent : IsDistSpec (GF := GF) E pl(&latent.fst #()) μ encode)
    (hdecoder : ∀ x, ⊢ tglWp E pl(&decoder.fst &(encode x).fst)
      (fun v : Val rT => iprop(⌜v = encode' (decode x)⌝)))
    (F : β → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ ↯ (∫⁻ y, F y ∂GenerativeModel.law μ decode) ∗ R -∗
      tglWp E pl(&Occil.General.generativeModel &latent.fst &decoder.fst #())
        (fun v : Val rT => iprop(∃ y : β, ⌜v = encode' y⌝ ∗ ↯ (F y) ∗ R)) := by
  let := GenerativeModel.law_prob μ decode hdecode
  exact frame (GenerativeModel.generativeModel_distSpec E μ latent decoder
    encode encode' decode hdecode hlatent hdecoder) F hF R

example : (∫⁻ b, (if b then 7 else ∞ : ℝ≥0∞)
    ∂GenerativeModel.law (RealCoin.law 0) Bool.not) = 7 := by
  rw [← GenerativeModel.expectation _ _ (measurable_of_countable _) _
    (measurable_of_countable _)]
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]

example : (∫⁻ b, (if b then ∞ else 0 : ℝ≥0∞)
    ∂GenerativeModel.law (RealCoin.law 0) Bool.not) = ∞ := by
  rw [← GenerativeModel.expectation _ _ (measurable_of_countable _) _
    (measurable_of_countable _)]
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]

example {α : Type _} [MeasurableSpace α] [ProbLangDist.IsUniformInt rT]
    (E : CoPset) (n : ℕ) [NeZero n] (quantile : Fin n → α)
    (encode : α → Val rT) (callback : Val rT)
    (hquantile : ∀ i : Fin n,
      ⊢ tglWp E pl(&callback.fst #int ((n + 1 : ℕ) : ℤ) #int ((i.val + 1 : ℕ) : ℤ))
        (fun v : Val rT => iprop(⌜v = encode (quantile i)⌝)))
    (F : α → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂InverseQuantile.law n quantile) ∗ R -∗
      tglWp E pl(&Occil.General.inverseQuantile #int ((n + 1 : ℕ) : ℤ) &callback.fst #())
        (fun v : Val rT => iprop(∃ x : α, ⌜v = encode x⌝ ∗ ↯ (F x) ∗ R)) :=
  frame (InverseQuantile.inverseQuantile_distSpec E n quantile encode callback hquantile) F hF R

example : (∫⁻ x, (if x = 17 then 7 else ∞ : ℝ≥0∞)
    ∂InverseQuantile.law 1 (fun _ => (17 : ℕ))) = 7 := by
  rw [← InverseQuantile.expectation _ _ _ (measurable_of_countable _)]
  norm_num

example : (∫⁻ x, (if x = 17 then 7 else ∞ : ℝ≥0∞)
    ∂InverseQuantile.law 2 (fun _ => (17 : ℕ))) = 7 := by
  rw [← InverseQuantile.expectation _ _ _ (measurable_of_countable _)]
  norm_num [Finset.sum_range_succ]
  rw [show (14 : ℝ≥0∞) = 7 * 2 by norm_num, ENNReal.mul_div_cancel_right] <;> norm_num

#print axioms GenerativeModel.generativeModel_distSpec
#print axioms GenerativeModel.expectation
#print axioms InverseQuantile.inverseQuantile_distSpec
#print axioms InverseQuantile.expectation


example [ProbLangDist.IsUniformInt rT] (E : CoPset) (xs : List ℤ) [NeZero xs.length]
    (kernel : MeasureTheory.Measure ℤ) [MeasureTheory.IsProbabilityMeasure kernel]
    (jitter : Val rT)
    (hjitter : IsDistSpec (GF := GF) E pl(&jitter.fst #()) kernel Val.int)
    (F : ℤ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂KernelDensity.law xs kernel) ∗ R -∗
      tglWp E pl(&Occil.General.kernelDensity
        &(listVal (fun z : ℤ => Val.int z) xs).fst &jitter.fst #())
        (fun v : Val rT => iprop(∃ x : ℤ, ⌜v = Val.int x⌝ ∗ ↯ (F x) ∗ R)) :=
  frame (KernelDensity.kernelDensity_distSpec E xs kernel jitter hjitter)
    F (measurable_of_countable _) R

example : (∫⁻ x, (if x = 1 then 1 else 0 : ℝ≥0∞)
    ∂KernelDensity.law [1, 1, 3] (MeasureTheory.Measure.dirac 0)) = 2 / 3 := by
  rw [← KernelDensity.expectation]
  simp [Choice.lintegral_law, Choice.position, List.get_eq_getElem,
    Finset.sum_range_succ]
  norm_num

example : (∫⁻ x, (if x = 5 then 7 else ∞ : ℝ≥0∞)
    ∂KernelDensity.law [7, 7] (MeasureTheory.Measure.dirac (-2))) = 7 := by
  rw [← KernelDensity.expectation]
  norm_num [Choice.lintegral_law, Choice.position, List.get_eq_getElem,
    Finset.sum_range_succ]
  rw [show (14 : ℝ≥0∞) = 7 * 2 by norm_num, ENNReal.mul_div_cancel_right] <;> norm_num

example (xs : List ℤ) [NeZero xs.length] (kernel : MeasureTheory.Measure ℤ)
    [MeasureTheory.IsProbabilityMeasure kernel] :
    (∫⁻ _ : ℤ, (∞ : ℝ≥0∞) ∂KernelDensity.law xs kernel) = ∞ := by
  simp

#print axioms KernelDensity.kernelDensity_distSpec
#print axioms KernelDensity.expectation


example {α : Type _} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {E : CoPset} {e : Exp rT}
    {encode : α → Val rT} (h : IsDistSpec (GF := GF) E e μ encode)
    (P : α → Prop) (hP : MeasurableSet {x | P x}) (hs : ∀ᵐ x ∂μ, P x)
    (F : α → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂μ) ∗ R -∗ tglWp E e
      (fun v : Val rT => iprop(∃ x : α,
        ⌜P x ∧ v = encode x⌝ ∗ ↯ (F x) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply (h.wp_supported P hP hs F hF _) $$ Hcredit
  iintro %x %hx Hcredit
  iexists x
  iframe Hcredit HR
  ipureintro
  exact ⟨hx, rfl⟩

example : ∀ᵐ b ∂RealCoin.law 0, b = false := by
  simp [RealCoin.law, RealCoin.pmf]

example [ProbLangDist.IsUniformInt rT] (E : CoPset) (scale dimension : ℕ)
    [NeZero scale] (F : List ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ ys, F ys ∂UniformBoxPoint.law scale dimension) ∗ R -∗
      tglWp E pl(&Occil.General.uniformBoxPoint #int (scale : ℤ) #int (dimension : ℤ))
        (fun v : Val rT => iprop(∃ ys : List ℕ,
          ⌜v = listVal (fun n : ℕ => Val.int n) ys⌝ ∗ ↯ (F ys) ∗ R)) :=
  frame (UniformBoxPoint.uniformBoxPoint_distSpec E scale dimension)
    F (measurable_of_countable _) R

example (scale : ℕ) [NeZero scale] :
    (∫⁻ ys, (if ys = [] then 7 else ∞ : ℝ≥0∞)
      ∂UniformBoxPoint.law scale 0) = 7 := by
  simp [UniformBoxPoint.law, ListProduct.law]

example : (∫⁻ ys, (if ys = [0, 0] then 7 else ∞ : ℝ≥0∞)
    ∂UniformBoxPoint.law 1 2) = 7 := by
  rw [← UniformBoxPoint.expectation 1 1]
  simp only [UniformInt.lintegral_law, Finset.sum_range_one]
  rw [← UniformBoxPoint.expectation 1 0]
  simp [UniformBoxPoint.law, ListProduct.law, UniformInt.lintegral_law]

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (xs : List Bool) (F : List Bool → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ ys, F ys ∂FlipBits.law p xs) ∗ R -∗
      tglWp E pl(&Occil.flipBits &(listVal Val.bool xs).fst &coin.fst)
        (fun v : Val rT => iprop(∃ ys : List Bool,
          ⌜v = listVal Val.bool ys⌝ ∗ ↯ (F ys) ∗ R)) :=
  frame (FlipBits.flipBits_distSpec E p coin hcoin xs) F (measurable_of_countable _) R

example (xs : List Bool) : FlipBits.law 0 xs = MeasureTheory.Measure.dirac xs := by
  induction xs with
  | nil => rfl
  | cons x xs IH => simp [FlipBits.law, RealCoin.law, RealCoin.pmf, FlipBits.flip, IH,
      MeasureTheory.Measure.dirac_prod_dirac, MeasureTheory.Measure.map_dirac]

example (xs : List Bool) :
    FlipBits.law 1 xs = MeasureTheory.Measure.dirac (xs.map Bool.not) := by
  induction xs with
  | nil => rfl
  | cons x xs IH => simp [FlipBits.law, RealCoin.law, RealCoin.pmf, FlipBits.flip, IH,
      MeasureTheory.Measure.dirac_prod_dirac, MeasureTheory.Measure.map_dirac]

example : (∫⁻ ys, (if ys = [false] then ∞ else 0 : ℝ≥0∞)
    ∂FlipBits.law 1 [true]) = ∞ := by
  simp [FlipBits.law, RealCoin.law, RealCoin.pmf, FlipBits.flip,
    MeasureTheory.Measure.dirac_prod_dirac, MeasureTheory.Measure.map_dirac]

example (p : unitInterval) : (∫⁻ ys, (if ys = [] then 7 else ∞ : ℝ≥0∞)
    ∂FlipBits.law p []) = 7 := by
  simp [FlipBits.law]

#print axioms IsDistSpec.wp_supported
#print axioms UniformBoxPoint.uniformBoxPoint_distSpec
#print axioms UniformBoxPoint.expectation
#print axioms ListProduct.expectation
#print axioms FlipBits.flipBits_distSpec
#print axioms FlipBits.expectation

end

end ReviewExpansionStructured
