import SampLib.Samplers.MarkovTrajectory
import SampLib.Samplers.GibbsSweep
import SampLib.Samplers.RandomScanGibbs
import SampLib.Samplers.StoppedMinimum
import SampLib.Samplers.StoppedMaximum

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
    (counter sample : Val rT) (hp : ∀ᵐ n ∂ν, 0 < n)
    (hc : IsDistSpec (GF := GF) E pl(&counter.fst #()) ν (fun n => Val.int (n : ℤ)))
    (hs : IsDistSpec (GF := GF) E pl(&sample.fst #()) μ Val.int)
    (F : ℤ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂StoppedExtrema.law true ν μ) ∗ R -∗
      tglWp E pl(&Occil.General.stoppedMinimum &counter.fst &sample.fst #())
        (fun v : Val rT => iprop(∃ x : ℤ, ⌜v = Val.int x⌝ ∗ ↯ (F x) ∗ R)) :=
  frame (StoppedMinimum.stoppedMinimum_distSpec E ν μ counter sample hp hc hs)
    F (measurable_of_countable _) R

example (E : CoPset) (ν : MeasureTheory.Measure ℕ) [MeasureTheory.IsProbabilityMeasure ν]
    (μ : MeasureTheory.Measure ℤ) [MeasureTheory.IsProbabilityMeasure μ]
    (counter sample : Val rT) (hp : ∀ᵐ n ∂ν, 0 < n)
    (hc : IsDistSpec (GF := GF) E pl(&counter.fst #()) ν (fun n => Val.int (n : ℤ)))
    (hs : IsDistSpec (GF := GF) E pl(&sample.fst #()) μ Val.int)
    (F : ℤ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂StoppedExtrema.law false ν μ) ∗ R -∗
      tglWp E pl(&Occil.General.stoppedMaximum &counter.fst &sample.fst #())
        (fun v : Val rT => iprop(∃ x : ℤ, ⌜v = Val.int x⌝ ∗ ↯ (F x) ∗ R)) :=
  frame (StoppedMaximum.stoppedMaximum_distSpec E ν μ counter sample hp hc hs)
    F (measurable_of_countable _) R

section integer_draws
variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) (rows : List MarkovChain.Row)
    (hsq : ∀ r ∈ rows, r.val.length = rows.length) (n i : ℕ) (hi : i < rows.length)
    (F : List ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ xs, F xs ∂MarkovTrajectory.law rows n i) ∗ R -∗
      tglWp E pl(&Occil.General.markovTrajectory &(listVal MarkovChain.encodeRow rows).fst
        #int (i : ℤ) #int (n : ℤ))
        (fun v : Val rT => iprop(∃ xs : List ℕ,
          ⌜v = listVal (fun k : ℕ => Val.int k) xs⌝ ∗ ↯ (F xs) ∗ R)) :=
  frame (MarkovTrajectory.markovTrajectory_distSpec E rows hsq n i hi)
    F (measurable_of_countable _) R

example {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (E : CoPset) (d : ℕ) [NeZero d] (conditional : Val rT) (encode : α → Val rT)
    (K : Fin d → α → MeasureTheory.Measure α)
    [∀ i x, MeasureTheory.IsProbabilityMeasure (K i x)]
    (hc : ∀ i x, IsDistSpec (GF := GF) E
      pl(&conditional.fst #int (i.val : ℤ) &(encode x).fst) (K i x) encode)
    (n : ℕ) (x : α) (F : α → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂RandomScanGibbs.law d K n x) ∗ R -∗
      tglWp E pl(&Occil.General.randomScanGibbs #int (d : ℤ)
        &conditional.fst &(encode x).fst #int (n : ℤ))
        (fun v : Val rT => iprop(∃ z : α, ⌜v = encode z⌝ ∗ ↯ (F z) ∗ R)) :=
  frame (RandomScanGibbs.randomScanGibbs_distSpec E d conditional encode K hc n x)
    F (measurable_of_countable _) R

end integer_draws

example (E : CoPset) (matrix initial : Val rT) (F : Unit → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (F ()) ∗ R -∗ tglWp E
      pl(&Occil.General.markovTrajectory &matrix.fst &initial.fst #0)
      (fun v : Val rT => iprop(∃ u : Unit,
        ⌜v = listVal (fun k : ℕ => Val.int k) []⌝ ∗ ↯ (F u) ∗ R)) := by
  simpa using frame (MarkovTrajectory.markovTrajectory_zero_distSpec E matrix initial)
    F (measurable_of_countable _) R

example {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (E : CoPset) (d : ℕ) (conditional : Val rT) (encode : α → Val rT)
    (K : ℕ → α → MeasureTheory.Measure α)
    [∀ i x, MeasureTheory.IsProbabilityMeasure (K i x)]
    (hc : ∀ i < d, ∀ x, IsDistSpec (GF := GF) E
      pl(&conditional.fst #int (i : ℤ) &(encode x).fst) (K i x) encode)
    (x : α) (F : α → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂GibbsSweep.law K d x) ∗ R -∗
      tglWp E pl(&Occil.General.gibbsSweep #int (d : ℤ) &conditional.fst &(encode x).fst)
        (fun v : Val rT => iprop(∃ z : α, ⌜v = encode z⌝ ∗ ↯ (F z) ∗ R)) :=
  frame (GibbsSweep.gibbsSweep_distSpec E d conditional encode K hc x)
    F (measurable_of_countable _) R

example (E : CoPset) (d : ℕ) [NeZero d] (conditional initial : Val rT)
    (F : Unit → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (F ()) ∗ R -∗ tglWp E
      pl(&Occil.General.randomScanGibbs #int (d : ℤ) &conditional.fst &initial.fst #0)
      (fun v : Val rT => iprop(∃ u : Unit, ⌜v = initial⌝ ∗ ↯ (F u) ∗ R)) := by
  simpa using frame (RandomScanGibbs.randomScanGibbs_zero_distSpec E d conditional initial)
    F (measurable_of_countable _) R

example (E : CoPset) (conditional initial : Val rT) (F : Unit → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (F ()) ∗ R -∗ tglWp E
      pl(&Occil.General.gibbsSweep #0 &conditional.fst &initial.fst)
      (fun v : Val rT => iprop(∃ u : Unit, ⌜v = initial⌝ ∗ ↯ (F u) ∗ R)) := by
  have hc : ∀ (i : ℕ), i < 0 → ∀ x : Unit, IsDistSpec (GF := GF) E
      pl(&conditional.fst #int (i : ℤ) &initial.fst)
      (MeasureTheory.Measure.dirac x) (fun _ => initial) := by
    intro i hi
    exact False.elim (Nat.not_lt_zero i hi)
  simpa [GibbsSweep.law, FiniteKernels.sweep] using
    frame (GibbsSweep.gibbsSweep_distSpec E 0 conditional (fun _ : Unit => initial)
      (fun _ x => MeasureTheory.Measure.dirac x) hc ()) F (measurable_of_countable _) R

open MeasureTheory

example (b : Bool) (ν : Measure ℕ) [IsProbabilityMeasure ν]
    (μ : Measure ℤ) [IsProbabilityMeasure μ] :
    (∫⁻ _ : ℤ, (∞ : ℝ≥0∞) ∂StoppedExtrema.law b ν μ) = ∞ := by simp

example (b : Bool) (μ : Measure ℤ) (F : ℤ → ℝ≥0∞) :
    (∫⁻ x, F x ∂StoppedExtrema.law b (Measure.dirac 1) μ) = ∫⁻ x, F x ∂μ := by
  simp [StoppedExtrema.law, Measure.dirac_bind (measurable_of_countable _)]

example (b : Bool) (n : ℕ) (c : ℤ) :
    StoppedExtrema.tailLaw b (Measure.dirac c) n c = Measure.dirac c := by
  induction n with
  | zero => simp
  | succ n ih =>
    apply Measure.ext_of_lintegral
    intro F hF
    rw [← StoppedExtrema.tail_expectation]
    simp [StoppedExtrema.combine, ih]

example : GibbsSweep.law (fun i (x : ℤ) => Measure.dirac (10 * x + i)) 2 1 =
    Measure.dirac 101 := by
  simp [GibbsSweep.law, FiniteKernels.sweep,
    Measure.dirac_bind (measurable_of_countable _)]

example : RandomScanGibbs.law 1 (fun _ (x : ℤ) => Measure.dirac (x + 1)) 3 5 =
    Measure.dirac 8 := by
  simp [RandomScanGibbs.law, RandomScanGibbs.kernel, FiniteKernels.iterate,
    Choice.law,
    Measure.dirac_bind (measurable_of_countable _)]

example (d : ℕ) (μ : Measure ℤ) :
    μ.bind (GibbsSweep.law (fun _ x => Measure.dirac x) d) = μ :=
  FiniteKernels.sweep_invariant _ μ (fun _ => Measure.bind_dirac) 0 d

example (d : ℕ) [NeZero d] (μ : Measure ℤ) [IsProbabilityMeasure μ] (n : ℕ) :
    μ.bind (RandomScanGibbs.law d (fun _ x => Measure.dirac x) n) = μ :=
  RandomScanGibbs.invariant d _ μ (fun _ => Measure.bind_dirac) n

example {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (K : ℕ → α → Measure α) [∀ i x, IsProbabilityMeasure (K i x)] (d : ℕ) (x : α) :
    (∫⁻ _ : α, (∞ : ℝ≥0∞) ∂GibbsSweep.law K d x) = ∞ := by simp [GibbsSweep.law]

example {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (d : ℕ) [NeZero d] (K : Fin d → α → Measure α)
    [∀ i x, IsProbabilityMeasure (K i x)] (n : ℕ) (x : α) :
    (∫⁻ _ : α, (∞ : ℝ≥0∞) ∂RandomScanGibbs.law d K n x) = ∞ := by simp

private def alternating : List MarkovChain.Row :=
  [⟨[0, 1], by decide⟩, ⟨[1, 0], by decide⟩]

example : MarkovTrajectory.law alternating 3 0 = Measure.dirac [1, 0, 1] := by
  simp [MarkovTrajectory.law, FiniteKernels.trajectory, MarkovChain.kernel, MarkovChain.row,
    alternating, WeightedChoice.law, WeightedChoice.category, UniformInt.law,
    Measure.uniformOfFinset, Measure.map_dirac,
    Measure.dirac_bind (measurable_of_countable _)]

example (rows : List MarkovChain.Row) (n i : ℕ) :
    (∫⁻ _ : List ℕ, (∞ : ℝ≥0∞) ∂MarkovTrajectory.law rows n i) = ∞ := by simp

end
end ReviewExpansionStructured

#print axioms SampLib.StoppedMinimum.stoppedMinimum_distSpec
#print axioms SampLib.StoppedMaximum.stoppedMaximum_distSpec
#print axioms SampLib.StoppedExtrema.expectation
#print axioms SampLib.StoppedExtrema.tail_expectation

#print axioms SampLib.MarkovTrajectory.markovTrajectory_distSpec
#print axioms SampLib.MarkovTrajectory.markovTrajectory_zero_distSpec
#print axioms SampLib.GibbsSweep.gibbsSweep_distSpec
#print axioms SampLib.RandomScanGibbs.randomScanGibbs_distSpec
#print axioms SampLib.RandomScanGibbs.invariant

#print axioms SampLib.RandomScanGibbs.randomScanGibbs_zero_distSpec
