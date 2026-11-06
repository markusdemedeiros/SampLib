import SampLib.Discrete.PoissonRational
import Samplers.Discrete.Compound

/-! # Compound Poisson sums

The jumps may be arbitrary signed integers. A latent output type lets callers
reuse an existing count-valued jump specification without an encoding adapter.
-/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.CompoundPoisson

noncomputable section

section mathematics

open MeasureTheory Measure

variable {α : Type _} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

/-- Sum of independent integer-valued jumps. -/
def sumLaw (μ : Measure α) (jump : α → ℤ) : ℕ → Measure ℤ
  | 0 => dirac 0
  | n + 1 => (μ.prod (sumLaw μ jump n)).map (fun z => jump z.1 + z.2)

instance (μ : Measure α) [IsProbabilityMeasure μ] (jump : α → ℤ) (n : ℕ) :
    IsProbabilityMeasure (sumLaw μ jump n) := by
  induction n with
  | zero => dsimp [sumLaw]; infer_instance
  | succ n IH =>
    let := IH
    constructor
    rw [sumLaw, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

def sumCredit (μ : Measure α) (jump : α → ℤ) (n : ℕ) (total : ℤ)
    (F : ℤ → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ z, F (total + z) ∂sumLaw μ jump n

omit [Countable α] [MeasurableSingletonClass α] in
@[simp] theorem sumCredit_zero (μ : Measure α) (jump : α → ℤ) (total : ℤ)
    (F : ℤ → ℝ≥0∞) : sumCredit μ jump 0 total F = F total := by
  simp [sumCredit, sumLaw]

/-- The first independent jump advances the accumulator and leaves the tail sum. -/
theorem sum_expectation (μ : Measure α) [IsProbabilityMeasure μ] (jump : α → ℤ)
    (n : ℕ) (total : ℤ) (F : ℤ → ℝ≥0∞) :
    sumCredit μ jump (n + 1) total F =
      ∫⁻ x, sumCredit μ jump n (total + jump x) F ∂μ := by
  rw [sumCredit, sumLaw,
    lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]
  simp only [sumCredit, add_assoc]

/-- A Poisson number of independent jumps defines the compound Poisson law. -/
def law (rate : ℝ≥0) (μ : Measure α) (jump : α → ℤ) : Measure ℤ :=
  (ProbabilityTheory.poissonMeasure rate).bind (sumLaw μ jump)

instance (rate : ℝ≥0) (μ : Measure α) [IsProbabilityMeasure μ] (jump : α → ℤ) :
    IsProbabilityMeasure (law rate μ jump) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ
      (measurable_of_countable _).aemeasurable]
    simp

omit [Countable α] [MeasurableSingletonClass α] in
/-- Conditioning on the number of jumps preserves arbitrary continuation credits. -/
theorem expectation (rate : ℝ≥0) (μ : Measure α) [IsProbabilityMeasure μ]
    (jump : α → ℤ) (F : ℤ → ℝ≥0∞) :
    (∫⁻ n, sumCredit μ jump n 0 F ∂ProbabilityTheory.poissonMeasure rate) =
      ∫⁻ z, F z ∂law rate μ jump := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]
  simp only [sumCredit, zero_add]

end mathematics

theorem compoundPoisson_lc {rT : Type _} :
    (Occil.DiscreteExtra.compoundPoisson : Exp rT).IsLocallyClosed := by is_lc

theorem compoundPoisson_fv {rT : Type _} :
    (Occil.DiscreteExtra.compoundPoisson : Exp rT).fv = ∅ := by
  simp [Occil.DiscreteExtra.compoundPoisson, PoissonRational.poissonRational_fv, Exp.fv]

@[simp] theorem compoundPoisson_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.DiscreteExtra.compoundPoisson = Occil.DiscreteExtra.compoundPoisson :=
  (Exp.open_lc k e _ compoundPoisson_lc).symm

@[simp] theorem compoundPoisson_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.DiscreteExtra.compoundPoisson : Exp rT) =
      Occil.DiscreteExtra.compoundPoisson :=
  Exp.closeRec_fresh x _ k (by simp [compoundPoisson_fv])

private def loop {rT : Type _} [ProbLangℝ rT] (sampler : Val rT) : Exp rT :=
  .fix (.lam (.lam (pl%
    if {Exp.bvar 1} = #0 then {Exp.bvar 0} else
      {Exp.bvar 2} ({Exp.bvar 1} - #1) ({Exp.bvar 0} + &sampler.fst #()))))

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {α : Type _} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_loop (E : CoPset) (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure μ] (jump : α → ℤ) (sampler : Val rT)
    (hjump : IsDistSpec (GF := GF) E pl(&sampler.fst #()) μ (fun x => Val.int (jump x)))
    (n : ℕ) (total : ℤ) (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (sumCredit μ jump n total F) -∗
      tglWp E pl(&(loop sampler) #int (n : ℤ) #int total)
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z))) := by
  induction n generalizing total with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists total
    isimp only [sumCredit_zero] at Hcredit
    iframe Hcredit
    itrivial
  | succ n IH =>
    iintro Hcredit
    twp_pures
    twp_bind pl(&sampler.fst #())
    isimp only [sum_expectation] at Hcredit
    iapply (hjump.wp (fun x => sumCredit μ jump n (total + jump x) F)
      (measurable_of_countable _) _) $$ Hcredit
    iintro %x Hcredit
    iterate 2 twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    have h := IH (total + jump x)
    simp [loop] at h
    isimp [Exp.ofVal, Exp.close, Exp.closeRec]
    iapply h $$ Hcredit

theorem twp_compoundPoisson (E : CoPset) (x y : ℕ) (hy : 0 < y)
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (jump : α → ℤ) (sampler : Val rT)
    (hjump : IsDistSpec (GF := GF) E pl(&sampler.fst #()) μ (fun x => Val.int (jump x)))
    (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂law (PoissonRational.rate x y) μ jump) -∗
      tglWp E pl(&Occil.DiscreteExtra.compoundPoisson #int (x : ℤ) #int (y : ℤ)
        &sampler.fst)
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z))) := by
  iintro Hcredit
  iterate 3 twp_pure
  simp only [PoissonRational.poissonRational_openRec,
    PoissonRational.poissonRational_closeRec]
  twp_bind pl(&Occil.poissonRational #int (x : ℤ) #int (y : ℤ))
  isimp only [← expectation (PoissonRational.rate x y) μ jump F] at Hcredit
  iapply ((PoissonRational.poissonRational_distSpec E x y hy).wp
    (fun n => sumCredit μ jump n 0 F) (measurable_of_countable _) _) $$ Hcredit
  iintro %n Hcredit
  iterate 2 twp_pure
  have h := twp_loop (rT := rT) (GF := GF) E μ jump sampler hjump n 0 F
  simp [loop] at h
  iapply h $$ Hcredit

theorem compoundPoisson_distSpec (E : CoPset) (x y : ℕ) (hy : 0 < y)
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (jump : α → ℤ) (sampler : Val rT)
    (hjump : IsDistSpec (GF := GF) E pl(&sampler.fst #()) μ (fun x => Val.int (jump x))) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.compoundPoisson
      #int (x : ℤ) #int (y : ℤ) &sampler.fst)
      (law (PoissonRational.rate x y) μ jump) Val.int where
  spec F _ := wand_entails (twp_compoundPoisson E x y hy μ jump sampler hjump F)

end specification

end

end SampLib.CompoundPoisson
