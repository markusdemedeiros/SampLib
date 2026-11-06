import SampLib.Samplers.Choice
import SampLib.Samplers.ListMapSampling
import Samplers.General.DataModels

/-! # Vector empirical kernels with one shared center -/

open ProbLang
open scoped ENNReal

namespace SampLib.KernelDensityVector

noncomputable section

section mathematics

open MeasureTheory

/-- Translate the scalar kernel to one center coordinate. -/
def offsetLaw (kernel : Measure ℤ) (x : ℤ) : Measure ℤ := kernel.map (x + ·)

instance (kernel : Measure ℤ) [IsProbabilityMeasure kernel] (x : ℤ) :
    IsProbabilityMeasure (offsetLaw kernel x) where
  measure_univ := by
    rw [offsetLaw, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Choose one empirical vector, then perturb its coordinates independently. -/
def law (xs : List (List ℤ)) [NeZero xs.length] (kernel : Measure ℤ) :
    Measure (List ℤ) :=
  (Choice.law xs.length).bind (fun i => ListMapSampling.law (offsetLaw kernel) (xs.get i))

instance (xs : List (List ℤ)) [NeZero xs.length] (kernel : Measure ℤ)
    [IsProbabilityMeasure kernel] : IsProbabilityMeasure (law xs kernel) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
    simp

/-- Retaining the common center preserves its dependence across coordinates. -/
theorem expectation (xs : List (List ℤ)) [NeZero xs.length] (kernel : Measure ℤ)
    [IsProbabilityMeasure kernel] (F : List ℤ → ℝ≥0∞) :
    ∫⁻ i, ∫⁻ ys, F ys ∂ListMapSampling.law (offsetLaw kernel) (xs.get i)
      ∂Choice.law xs.length = ∫⁻ ys, F ys ∂law xs kernel := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]

end mathematics

private def addJitter {rT : Type _} [ProbLangℝ rT] (jitter : Val rT) : Val rT :=
  ⟨.lam (pl% {Exp.bvar 0} + &jitter.fst #()), .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem addJitter_spec (E : CoPset) (kernel : MeasureTheory.Measure ℤ)
    [MeasureTheory.IsProbabilityMeasure kernel] (jitter : Val rT)
    (hjitter : IsDistSpec (GF := GF) E pl(&jitter.fst #()) kernel Val.int) (x : ℤ) :
    IsDistSpec (GF := GF) E pl(&(addJitter jitter).fst #int x)
      (offsetLaw kernel x) Val.int where
  spec F _ := by
    iintro Hcredit
    twp_pure
    twp_bind pl(&jitter.fst #())
    isimp only [offsetLaw, MeasureTheory.lintegral_map
      (measurable_of_countable _) (measurable_of_countable _)] at Hcredit
    iapply (hjitter.wp (fun z => F (x + z)) (measurable_of_countable _) _) $$ Hcredit
    iintro %z Hcredit
    twp_pures
    twp_value
    imodintro
    iexists x + z
    iframe Hcredit
    itrivial

theorem twp_kernelDensityVector (E : CoPset) (xs : List (List ℤ)) [NeZero xs.length]
    (kernel : MeasureTheory.Measure ℤ) [MeasureTheory.IsProbabilityMeasure kernel]
    (jitter : Val rT)
    (hjitter : IsDistSpec (GF := GF) E pl(&jitter.fst #()) kernel Val.int)
    (F : List ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ ys, F ys ∂law xs kernel) -∗
      tglWp E pl(&Occil.General.kernelDensityVector
        &(listVal (listVal (fun z : ℤ => Val.int z)) xs).fst &jitter.fst #())
        (fun v : Val rT => iprop(∃ ys : List ℤ,
          ⌜v = listVal (fun z : ℤ => Val.int z) ys⌝ ∗ ↯ (F ys))) := by
  iintro Hcredit
  iterate 3 twp_pure
  twp_bind pl(&Occil.choice &(listVal (listVal (fun z : ℤ => Val.int z)) xs).fst)
  isimp only [← expectation xs kernel F] at Hcredit
  iapply ((Choice.choice_distSpec E (listVal (fun z : ℤ => Val.int z)) xs).wp
    (fun i => ∫⁻ ys, F ys ∂ListMapSampling.law (offsetLaw kernel) (xs.get i))
    (measurable_of_countable _) _) $$ Hcredit
  iintro %i Hcredit
  twp_pure
  twp_bind pl(&Occil.General.map &(addJitter jitter).fst
    &(listVal (fun z : ℤ => Val.int z) (xs.get i)).fst)
  iapply (tglWp_mono fun _ => tglWp_value)
  iapply (ListMapSampling.map_distSpec E (offsetLaw kernel) Val.int Val.int
    (addJitter jitter) (addJitter_spec E kernel jitter hjitter) (xs.get i)).spec
    F (measurable_of_countable _) $$ Hcredit

/-- Typed empirical vector kernel law; vectors may have different finite lengths. -/
theorem kernelDensityVector_distSpec (E : CoPset) (xs : List (List ℤ)) [NeZero xs.length]
    (kernel : MeasureTheory.Measure ℤ) [MeasureTheory.IsProbabilityMeasure kernel]
    (jitter : Val rT)
    (hjitter : IsDistSpec (GF := GF) E pl(&jitter.fst #()) kernel Val.int) :
    IsDistSpec (GF := GF) E pl(&Occil.General.kernelDensityVector
      &(listVal (listVal (fun z : ℤ => Val.int z)) xs).fst &jitter.fst #())
      (law xs kernel) (listVal (fun z : ℤ => Val.int z)) where
  spec F _ := wand_entails (twp_kernelDensityVector E xs kernel jitter hjitter F)

end specification

end

end SampLib.KernelDensityVector
