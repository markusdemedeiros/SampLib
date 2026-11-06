import SampLib.Combinatorial.Choice
import Samplers.General.DataModels

/-! # Empirical-center kernel sampling on integer grids -/

open ProbLang
open scoped ENNReal

namespace SampLib.KernelDensity

noncomputable section

section mathematics

open MeasureTheory

/-- An empirical center and an independent kernel offset. -/
def law (xs : List ℤ) [NeZero xs.length] (kernel : Measure ℤ) : Measure ℤ :=
  ((Choice.law xs.length).prod kernel).map (fun z => xs.get z.1 + z.2)

instance (xs : List ℤ) [NeZero xs.length] (kernel : Measure ℤ)
    [IsProbabilityMeasure kernel] : IsProbabilityMeasure (law xs kernel) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Conditioning on the empirical center gives its translated kernel expectation. -/
theorem expectation (xs : List ℤ) [NeZero xs.length] (kernel : Measure ℤ)
    [IsProbabilityMeasure kernel] (F : ℤ → ℝ≥0∞) :
    ∫⁻ i, ∫⁻ z, F (xs.get i + z) ∂kernel ∂Choice.law xs.length =
      ∫⁻ x, F x ∂law xs kernel := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_kernelDensity (E : CoPset) (xs : List ℤ) [NeZero xs.length]
    (kernel : MeasureTheory.Measure ℤ) [MeasureTheory.IsProbabilityMeasure kernel]
    (jitter : Val rT)
    (hjitter : IsDistSpec (GF := GF) E pl(&jitter.fst #()) kernel Val.int)
    (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ x, F x ∂law xs kernel) -∗
      tglWp E pl(&Occil.General.kernelDensity
        &(listVal (fun z : ℤ => Val.int z) xs).fst &jitter.fst #())
        (fun v : Val rT => iprop(∃ x : ℤ, ⌜v = Val.int x⌝ ∗ ↯ (F x))) := by
  iintro Hcredit
  iterate 3 twp_pure
  twp_bind pl(&Occil.choice &(listVal (fun z : ℤ => Val.int z) xs).fst)
  isimp only [← expectation xs kernel F] at Hcredit
  iapply ((Choice.choice_distSpec E (fun z : ℤ => Val.int z) xs).wp
    (fun i => ∫⁻ z, F (xs.get i + z) ∂kernel) (measurable_of_countable _) _) $$ Hcredit
  iintro %i Hcredit
  twp_pure
  twp_bind pl(&jitter.fst #())
  iapply (hjitter.wp (fun z => F (xs.get i + z)) (measurable_of_countable _) _) $$ Hcredit
  iintro %z Hcredit
  twp_pures
  twp_value
  imodintro
  iexists xs.get i + z
  iframe Hcredit
  itrivial

/-- Typed empirical-kernel convolution specification. -/
theorem kernelDensity_distSpec (E : CoPset) (xs : List ℤ) [NeZero xs.length]
    (kernel : MeasureTheory.Measure ℤ) [MeasureTheory.IsProbabilityMeasure kernel]
    (jitter : Val rT)
    (hjitter : IsDistSpec (GF := GF) E pl(&jitter.fst #()) kernel Val.int) :
    IsDistSpec (GF := GF) E pl(&Occil.General.kernelDensity
      &(listVal (fun z : ℤ => Val.int z) xs).fst &jitter.fst #())
      (law xs kernel) Val.int where
  spec F _ := wand_entails (twp_kernelDensity E xs kernel jitter hjitter F)

end specification

end

end SampLib.KernelDensity
