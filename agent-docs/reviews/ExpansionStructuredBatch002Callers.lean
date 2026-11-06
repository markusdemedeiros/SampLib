import SampLib.Templates
import SampLib.ListEncoding
import SampLib.Samplers.StoppedSum
import SampLib.Samplers.Episodes
import SampLib.Samplers.KernelDensityVector
import SampLib.Samplers.Stratified1D
import SampLib.Samplers.RandomString
import SampLib.Samplers.RandomDateTime
import SampLib.Samplers.ExpHalfCoin
import SampLib.Samplers.GaussianInteger
import SampLib.Samplers.GaussianSelector

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


example (E : CoPset) (ν : MeasureTheory.Measure ℕ) [MeasureTheory.IsProbabilityMeasure ν]
    (μ : MeasureTheory.Measure ℤ) [MeasureTheory.IsProbabilityMeasure μ]
    (counter sample : Val rT)
    (hcounter : IsDistSpec (GF := GF) E pl(&counter.fst #()) ν (fun n => Val.int (n : ℤ)))
    (hsample : IsDistSpec (GF := GF) E pl(&sample.fst #()) μ Val.int)
    (F : ℤ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂StoppedSum.law ν μ) ∗ R -∗
      tglWp E pl(&Occil.General.stoppedSum &counter.fst &sample.fst #())
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z) ∗ R)) :=
  frame (StoppedSum.stoppedSum_distSpec E ν μ counter sample hcounter hsample)
    F (measurable_of_countable _) R

example (E : CoPset) (ν : MeasureTheory.Measure ℕ) [MeasureTheory.IsProbabilityMeasure ν]
    (μ : MeasureTheory.Measure ℤ) [MeasureTheory.IsProbabilityMeasure μ]
    (counter sample : Val rT)
    (hcounter : IsDistSpec (GF := GF) E pl(&counter.fst #()) ν (fun n => Val.int (n : ℤ)))
    (hsample : IsDistSpec (GF := GF) E pl(&sample.fst #()) μ Val.int)
    (F : ℤ × ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ p, F p ∂Episodes.law ν μ) ∗ R -∗
      tglWp E pl(&Occil.General.episodes &counter.fst &sample.fst #())
        (fun v : Val rT => iprop(∃ p : ℤ × ℕ,
          ⌜v = Episodes.encode p⌝ ∗ ↯ (F p) ∗ R)) :=
  frame (Episodes.episodes_distSpec E ν μ counter sample hcounter hsample)
    F (measurable_of_countable _) R

private theorem sum_of_ones (n : ℕ) :
    StoppedSum.sumLaw (MeasureTheory.Measure.dirac (1 : ℤ)) n =
      MeasureTheory.Measure.dirac (n : ℤ) := by
  induction n with
  | zero => rfl
  | succ n IH =>
    simp [StoppedSum.sumLaw, IH, MeasureTheory.Measure.dirac_prod_dirac,
      MeasureTheory.Measure.map_dirac, Nat.cast_add, add_comm]

example (μ : MeasureTheory.Measure ℤ) [MeasureTheory.IsProbabilityMeasure μ] :
    (∫⁻ z, (if z = 0 then 7 else ∞ : ℝ≥0∞)
      ∂StoppedSum.law (MeasureTheory.Measure.dirac 0) μ) = 7 := by
  rw [← StoppedSum.expectation]
  simp [StoppedSum.sumLaw]

example (ν : MeasureTheory.Measure ℕ) [MeasureTheory.IsProbabilityMeasure ν] :
    (∫⁻ p, (if p.1 = (p.2 : ℤ) then 7 else ∞ : ℝ≥0∞)
      ∂Episodes.law ν (MeasureTheory.Measure.dirac 1)) = 7 := by
  rw [← Episodes.expectation]
  simp [sum_of_ones]

example (ν : MeasureTheory.Measure ℕ) [MeasureTheory.IsProbabilityMeasure ν]
    (μ : MeasureTheory.Measure ℤ) [MeasureTheory.IsProbabilityMeasure μ] :
    (∫⁻ _ : ℤ, (∞ : ℝ≥0∞) ∂StoppedSum.law ν μ) = ∞ := by simp

example [ProbLangDist.IsUniformInt rT] (E : CoPset) (xs : List (List ℤ))
    [NeZero xs.length] (kernel : MeasureTheory.Measure ℤ)
    [MeasureTheory.IsProbabilityMeasure kernel] (jitter : Val rT)
    (hjitter : IsDistSpec (GF := GF) E pl(&jitter.fst #()) kernel Val.int)
    (F : List ℤ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ ys, F ys ∂KernelDensityVector.law xs kernel) ∗ R -∗
      tglWp E pl(&Occil.General.kernelDensityVector
        &(listVal (listVal (fun z : ℤ => Val.int z)) xs).fst &jitter.fst #())
        (fun v : Val rT => iprop(∃ ys : List ℤ,
          ⌜v = listVal (fun z : ℤ => Val.int z) ys⌝ ∗ ↯ (F ys) ∗ R)) :=
  frame (KernelDensityVector.kernelDensityVector_distSpec E xs kernel jitter hjitter)
    F (measurable_of_countable _) R

private theorem zero_jitter (x : ℤ) :
    KernelDensityVector.offsetLaw (MeasureTheory.Measure.dirac 0) x =
      MeasureTheory.Measure.dirac x := by
  simp [KernelDensityVector.offsetLaw, MeasureTheory.Measure.map_dirac]

example : (∫⁻ ys, (if ys = [0, 0] then ∞ else 7 : ℝ≥0∞)
    ∂KernelDensityVector.law [[0, 10], [10, 0]] (MeasureTheory.Measure.dirac 0)) = 7 := by
  rw [← KernelDensityVector.expectation]
  have hz : KernelDensityVector.offsetLaw (MeasureTheory.Measure.dirac 0) =
      fun x : ℤ => MeasureTheory.Measure.dirac x := funext zero_jitter
  rw [hz]
  simp_rw [ListMapSampling.law_dirac (fun x : ℤ => x)]
  norm_num [Choice.lintegral_law, Choice.position, List.get_eq_getElem,
    Finset.sum_range_succ]
  rw [show (14 : ℝ≥0∞) = 7 * 2 by norm_num, ENNReal.mul_div_cancel_right] <;> norm_num

example : (∫⁻ ys, (if ys = [] then 7 else ∞ : ℝ≥0∞)
    ∂KernelDensityVector.law [[]] (MeasureTheory.Measure.dirac (-3))) = 7 := by
  rw [← KernelDensityVector.expectation]
  simp [List.get_eq_getElem, ListMapSampling.law]

example [ProbLangDist.IsUniformInt rT] (E : CoPset) (scale strata : ℕ)
    (hs : 0 < strata) (h : strata ≤ scale) (F : List ℤ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ ys, F ys ∂Stratified1D.law scale strata hs h) ∗ R -∗
      tglWp E pl(&Occil.General.stratified1D #int (scale : ℤ) #int (strata : ℤ) #())
        (fun v : Val rT => iprop(∃ ys : List ℤ,
          ⌜v = listVal Val.int ys⌝ ∗ ↯ (F ys) ∗ R)) :=
  frame (Stratified1D.stratified1D_distSpec E scale strata hs h)
    F (measurable_of_countable _) R

example : Stratified1D.boundary 7 3 0 = 0 ∧ Stratified1D.boundary 7 3 1 = 2 ∧
    Stratified1D.boundary 7 3 2 = 4 ∧ Stratified1D.boundary 7 3 3 = 7 := by decide

example (i : ℕ) : Stratified1D.boundary 7 7 i = i := by
  simp [Stratified1D.boundary]

example : (∫⁻ ys, (if ys = [0] then 7 else ∞ : ℝ≥0∞)
    ∂Stratified1D.law 1 1 (by decide) (by decide)) = 7 := by
  simp [Stratified1D.law, ListProduct.law, Stratified1D.coordinate,
    Stratified1D.boundary, RndIntExcRange.law, UniformInt.law,
    MeasureTheory.Measure.uniformOfFinset, MeasureTheory.Measure.dirac_prod_dirac,
    MeasureTheory.Measure.map_dirac]

example : (∫⁻ _ : List ℤ, (∞ : ℝ≥0∞)
    ∂Stratified1D.law 1 1 (by decide) (by decide)) = ∞ := by simp

example {α : Type _} [ProbLangDist.IsUniformInt rT] (E : CoPset)
    (encode : α → Val rT) (xs : List α) [NeZero xs.length] (n : ℕ)
    (F : (Fin n → Fin xs.length) → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ ys, F ys ∂SampleWithReplacement.law (Choice.law xs.length) n) ∗ R -∗
      tglWp E pl(&Occil.General.randomString &(listVal encode xs).fst #int (n : ℤ))
        (fun v : Val rT => iprop(∃ ys : Fin n → Fin xs.length,
          ⌜v = listVal (fun i => encode (xs.get i)) (List.ofFn ys)⌝ ∗ ↯ (F ys) ∗ R)) :=
  frame (RandomString.randomString_distSpec E encode xs n)
    F (measurable_of_countable _) R

example {α : Type _} (E : CoPset) (encode : α → Val rT)
    (F : Unit → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ u, F u ∂MeasureTheory.Measure.dirac ()) ∗ R -∗
      tglWp E pl(&Occil.General.randomString &(listVal encode []).fst #int (0 : ℤ))
        (fun v : Val rT => iprop(∃ u : Unit,
          ⌜v = listVal encode []⌝ ∗ ↯ (F u) ∗ R)) :=
  frame (RandomString.randomString_zero_distSpec E encode []) F (measurable_of_countable _) R

example : (∫⁻ ys, (if ([1, 1, 3] : List ℕ).get (ys 0) = 1 then 1 else 0 : ℝ≥0∞)
    ∂SampleWithReplacement.law (Choice.law 3) 1) = 2 / 3 := by
  rw [SampleWithReplacement.lintegral_law_succ _ 0 _ (measurable_of_countable _)]
  norm_num [SampleWithReplacement.law, Choice.lintegral_law, Choice.position,
    List.get_eq_getElem, Finset.sum_range_succ]

example [ProbLangDist.IsUniformInt rT] (E : CoPset) (lo hi : ℤ) (h : lo ≤ hi)
    (F : ℤ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂RndIntRange.law lo hi) ∗ R -∗
      tglWp E pl(&Occil.General.randomDateTime #int lo #int hi)
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z) ∗ R)) :=
  frame (RandomDateTime.randomDateTime_distSpec E lo hi h) F (measurable_of_countable _) R

example : (∫⁻ z, (if z = -7 then 7 else ∞ : ℝ≥0∞)
    ∂RndIntRange.law (-7) (-7)) = 7 := by
  rw [← RndIntRange.expectation]
  simp [RndInt.expectation]

#print axioms StoppedSum.stoppedSum_distSpec
#print axioms StoppedSum.expectation
#print axioms Episodes.episodes_distSpec
#print axioms Episodes.expectation
#print axioms KernelDensityVector.kernelDensityVector_distSpec
#print axioms ListMapSampling.map_distSpec
#print axioms Stratified1D.stratified1D_distSpec
#print axioms RandomString.randomString_distSpec
#print axioms RandomString.randomString_zero_distSpec
#print axioms RandomDateTime.randomDateTime_distSpec

section real_model

variable [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
  [ErisGS ℝ hlc GF]

example (E : CoPset) (F : Bool → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂ExpHalfCoin.law) ∗ R -∗
      tglWp E pl(&Occil.expHalfCoin #())
        (fun v : Val ℝ => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ R)) :=
  frame (rT := ℝ) (ExpHalfCoin.expHalfCoin_distSpec E) F (measurable_of_countable _) R

example : (ExpHalfCoin.bias : ℝ) = Real.exp (-1 / 2) := rfl

example : ExpHalfCoin.law {true} = ENNReal.ofReal (Real.exp (-1 / 2)) := by
  simp [ExpHalfCoin.law, ExpHalfCoin.bias, RealCoin.law, RealCoin.pmf,
    TotalEris.Examples.γBNE]

example : (∫⁻ _ : Bool, (∞ : ℝ≥0∞) ∂ExpHalfCoin.law) = ∞ := by
  rw [MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one]

example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂GaussianInteger.law) ∗ R -∗
      tglWp E pl(&Occil.gaussianInteger #())
        (fun v : Val ℝ => iprop(∃ k : ℕ, ⌜v = Val.int k⌝ ∗ ↯ (F k) ∗ R)) :=
  frame (rT := ℝ) (GaussianInteger.gaussianInteger_distSpec E) F (measurable_of_countable _) R

example : (∫⁻ k, (if k = 0 then 1 else 0 : ℝ≥0∞) ∂GaussianInteger.law) =
    TotalEris.Examples.G1PMF 0 := by
  simp [GaussianInteger.lintegral_law, TotalEris.Examples.G1CreditV]

example : (∫⁻ _ : ℕ, (∞ : ℝ≥0∞) ∂GaussianInteger.law) = ∞ := by simp

example : (GaussianSelector.bias 0 0 : ℝ) = 1 := by
  simp [GaussianSelector.bias, TotalEris.Examples.γBkx]

example : (GaussianSelector.bias 0 1 : ℝ) = Real.exp (-1 / 2) := by
  norm_num [GaussianSelector.bias, TotalEris.Examples.γBkx]

example : GaussianSelector.factor 0 = 2 := by
  apply Subtype.ext
  norm_num [GaussianSelector.factor]

#print axioms ExpHalfCoin.expHalfCoin_distSpec
#print axioms ExpHalfCoin.expectation
#print axioms GaussianInteger.gaussianInteger_distSpec
#print axioms GaussianInteger.expectation
#print axioms GaussianSelector.twp_gaussianSelector
#print axioms GaussianSelector.expectation

end real_model

end

end ReviewExpansionStructured
