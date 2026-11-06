import SampLib.Discrete.CompoundPoisson
import SampLib.Discrete.Skellam
import SampLib.Discrete.NeymanTypeA
import SampLib.Discrete.PolyaAeppli
import SampLib.Discrete.ZeroTruncatedPoisson
import Metrology.Iris.LocalBI

/-! Independent signed-jump and conditional-count clients. -/

open Set ProbLang
open scoped ENNReal NNReal

namespace ExpansionDiscreteAudit

noncomputable section

section mathematics

open MeasureTheory Measure SampLib

example : CompoundPoisson.sumLaw (dirac (-1 : ℤ)) id 2 = dirac (-2) := by
  simp [CompoundPoisson.sumLaw, Measure.dirac_prod_dirac,
    Measure.map_dirac' (measurable_of_countable _)]

example (F : ℤ → ℝ≥0∞) :
    CompoundPoisson.sumCredit (dirac (-3 : ℤ)) id 2 1 F = F (-5) := by
  simp [CompoundPoisson.sumCredit, CompoundPoisson.sumLaw, Measure.dirac_prod_dirac,
    Measure.map_dirac' (measurable_of_countable _)]

example (μ : Measure ℤ) [IsProbabilityMeasure μ] :
    CompoundPoisson.law 0 μ id = dirac 0 := by
  rw [CompoundPoisson.law, Distributions.poissonMeasure_zero,
    Measure.dirac_bind (measurable_of_countable _)]
  rfl

example (rate : ℝ≥0) (μ : Measure ℤ) [IsProbabilityMeasure μ] :
    (∫⁻ _z, (∞ : ℝ≥0∞) ∂CompoundPoisson.law rate μ id) = ∞ := by simp

example : Skellam.law 0 0 = dirac 0 := by
  simp [Skellam.law, Distributions.poissonMeasure_zero, Measure.dirac_prod_dirac,
    Measure.map_dirac' (measurable_of_countable _)]

example (r : ℝ≥0) (F : ℤ → ℝ≥0∞) :
    (∫⁻ z, F z ∂Skellam.law 0 r) =
      ∫⁻ k, F (-(k : ℤ)) ∂ProbabilityTheory.poissonMeasure r := by
  rw [← Skellam.expectation]
  simp [Distributions.poissonMeasure_zero]

example (r s : ℝ≥0) : (∫⁻ _z, (∞ : ℝ≥0∞) ∂Skellam.law r s) = ∞ := by simp

example (r : ℝ≥0) : NeymanTypeA.law 0 r = dirac 0 := by
  rw [NeymanTypeA.law, CompoundPoisson.law, Distributions.poissonMeasure_zero,
    Measure.dirac_bind (measurable_of_countable _)]
  rfl

example (p : unitInterval) : PolyaAeppli.law 0 p = dirac 0 := by
  rw [PolyaAeppli.law, CompoundPoisson.law, Distributions.poissonMeasure_zero,
    Measure.dirac_bind (measurable_of_countable _)]
  rfl

example : (PolyaAeppli.jumpBias 3 3 (by decide) (by decide) : ℝ) = 1 := by
  norm_num [PolyaAeppli.jumpBias, PoissonRational.bias, RationalCoin.bias]

example (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    ZeroTruncatedPoisson.law x y hx hy {0} = 0 := by
  simp [ZeroTruncatedPoisson.law, Rejection.law,
    Measure.restrict_apply, ZeroTruncatedPoisson.acceptance]

example (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    (∫⁻ k, (if k = 0 then ∞ else 0 : ℝ≥0∞)
      ∂ZeroTruncatedPoisson.law x y hx hy) = 0 := by
  rw [ZeroTruncatedPoisson.law, Rejection.law, lintegral_smul_measure]
  have hzero : (∫⁻ k in ZeroTruncatedPoisson.acceptance,
      (if k = 0 then ∞ else 0 : ℝ≥0∞)
        ∂ProbabilityTheory.poissonMeasure (PoissonRational.rate x y)) = 0 := by
    calc
      _ = ∫⁻ _k in ZeroTruncatedPoisson.acceptance, (0 : ℝ≥0∞)
          ∂ProbabilityTheory.poissonMeasure (PoissonRational.rate x y) := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro k hk
        simp [ne_of_gt (Set.mem_Ioi.mp hk)]
      _ = 0 := by simp
  rw [hzero, smul_eq_mul, mul_zero]

example (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    (∫⁻ _k, (∞ : ℝ≥0∞) ∂ZeroTruncatedPoisson.law x y hx hy) = ∞ := by simp

end mathematics

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


example (E : CoPset) (x y : ℕ) (hy : 0 < y) (μ : MeasureTheory.Measure ℤ)
    [MeasureTheory.IsProbabilityMeasure μ] (sampler : Val rT)
    (hjump : IsDistSpec (GF := GF) E pl(&sampler.fst #()) μ Val.int)
    (F : ℤ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂CompoundPoisson.law (PoissonRational.rate x y) μ id) ∗ I -∗
      tglWp E pl(&Occil.DiscreteExtra.compoundPoisson #int (x : ℤ) #int (y : ℤ)
        &sampler.fst)
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z) ∗ I)) :=
  frame (CompoundPoisson.compoundPoisson_distSpec E x y hy μ id sampler hjump) F I

example (E : CoPset) (a b c d : ℕ) (hb : 0 < b) (hd : 0 < d)
    (F : ℤ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂Skellam.law (PoissonRational.rate a b)
      (PoissonRational.rate c d)) ∗ I -∗
      tglWp E pl(&Occil.DiscreteExtra.skellam
        #int (a : ℤ) #int (b : ℤ) #int (c : ℤ) #int (d : ℤ))
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z) ∗ I)) :=
  frame (Skellam.skellam_distSpec E a b c d hb hd) F I

example (E : CoPset) (a b c d : ℕ) (hb : 0 < b) (hd : 0 < d)
    (F : ℤ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂NeymanTypeA.law (PoissonRational.rate a b)
      (PoissonRational.rate c d)) ∗ I -∗
      tglWp E pl(&Occil.DiscreteExtra.neymanTypeA
        #int (a : ℤ) #int (b : ℤ) #int (c : ℤ) #int (d : ℤ))
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z) ∗ I)) :=
  frame (NeymanTypeA.neymanTypeA_distSpec E a b c d hb hd) F I

example (E : CoPset) (x y a b : ℕ) (hy : 0 < y) (ha : 0 < a) (hab : a ≤ b)
    (F : ℤ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂PolyaAeppli.law (PoissonRational.rate x y)
      (PolyaAeppli.jumpBias a b ha hab)) ∗ I -∗
      tglWp E pl(&Occil.DiscreteExtra.polyaAeppli
        #int (x : ℤ) #int (y : ℤ) #int (a : ℤ) #int (b : ℤ))
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z) ∗ I)) :=
  frame (PolyaAeppli.polyaAeppli_distSpec E x y a b hy ha hab) F I

example (E : CoPset) (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂ZeroTruncatedPoisson.law x y hx hy) ∗ I -∗
      tglWp E pl(&Occil.DiscreteExtra.zeroTruncatedPoisson #int (x : ℤ) #int (y : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (ZeroTruncatedPoisson.zeroTruncatedPoisson_distSpec E x y hx hy) F I

#print axioms CompoundPoisson.compoundPoisson_distSpec
#print axioms CompoundPoisson.expectation
#print axioms CompoundPoisson.sum_expectation
#print axioms Skellam.skellam_distSpec
#print axioms Skellam.expectation
#print axioms NeymanTypeA.neymanTypeA_distSpec
#print axioms PolyaAeppli.polyaAeppli_distSpec
#print axioms ZeroTruncatedPoisson.zeroTruncatedPoisson_distSpec
#print axioms ZeroTruncatedPoisson.expectation

end

end ExpansionDiscreteAudit
