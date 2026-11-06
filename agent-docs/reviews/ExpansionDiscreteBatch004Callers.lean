import SampLib.Discrete.PoissonRational
import SampLib.Discrete.Laws.BinomialThinning
import SampLib.Weighted.BitmaskRejection
import Metrology.Iris.LocalBI

/-! Independent rational-rate and bounded-rejection clients. -/

open Set ProbLang
open scoped ENNReal NNReal

namespace ExpansionDiscreteAudit

noncomputable section

section mathematics

open MeasureTheory Measure SampLib

example : (PoissonRational.rate 1 2 : ℝ) = 1 / 2 := by
  norm_num [PoissonRational.rate]

example (y : ℕ) : PoissonRational.rate 0 y = 0 := by simp [PoissonRational.rate]

example : PoissonRational.rate 6 2 = 3 := by norm_num [PoissonRational.rate]

example (y : ℕ) : ProbabilityTheory.poissonMeasure (PoissonRational.rate 0 y) = dirac 0 := by
  simp [PoissonRational.rate, Distributions.poissonMeasure_zero]

example (r : ℝ≥0) :
    (ProbabilityTheory.poissonMeasure r).bind (fun n => ProbabilityTheory.binomial n 0) =
      dirac 0 := by
  rw [Distributions.poissonMeasure_bind_binomial]
  simp [Distributions.poissonMeasure_zero]

example (r : ℝ≥0) :
    (ProbabilityTheory.poissonMeasure r).bind (fun n => ProbabilityTheory.binomial n 1) =
      ProbabilityTheory.poissonMeasure r := by
  rw [Distributions.poissonMeasure_bind_binomial]
  simp

example :
    (ProbabilityTheory.poissonMeasure 1).bind (fun n => ProbabilityTheory.binomial n
      (PoissonRational.bias 1 2 (by decide) (by decide))) =
      ProbabilityTheory.poissonMeasure (PoissonRational.rate 1 2) := by
  rw [Distributions.poissonMeasure_bind_binomial, PoissonRational.bias_rate, one_mul]

example (x y : ℕ) : (∫⁻ _k : ℕ, (∞ : ℝ≥0∞)
    ∂ProbabilityTheory.poissonMeasure (PoissonRational.rate x y)) = ∞ := by simp

example : PowerOfTwoCeiling.width 1 = 1 := by norm_num [PowerOfTwoCeiling.width]
example : PowerOfTwoCeiling.width 4 = 4 := by decide
example : PowerOfTwoCeiling.width 5 = 8 := by decide

example : UniformInt.law 1 = dirac 0 := by simp [UniformInt.law, Measure.uniformOfFinset]

example : (∫⁻ k, (if k = 0 then 0 else ∞ : ℝ≥0∞) ∂UniformInt.law 1) = 0 := by
  simp [UniformInt.law, Measure.uniformOfFinset]

example (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ k, UniformRejection.kernel 4 F ε k ∂UniformInt.law 4) =
      ∫⁻ k, F k ∂UniformInt.law 4 := by
  simp only [UniformInt.lintegral_law]
  congr 1

example (p : unitInterval) (n : ℕ) (F : ℕ → ℝ≥0∞) :
    (∫⁻ k, (∫⁻ j, F j ∂Binomial.law 0 k) ∂Binomial.law p n) = F 0 := by
  simp

example (p : unitInterval) (n : ℕ) (F : ℕ → ℝ≥0∞) :
    (∫⁻ k, (∫⁻ j, F j ∂Binomial.law 1 k) ∂Binomial.law p n) =
      ∫⁻ j, F j ∂Binomial.law p n := by
  simp

example (p q : unitInterval) (n : ℕ) :
    (∫⁻ k, (∫⁻ _j, (∞ : ℝ≥0∞) ∂Binomial.law q k) ∂Binomial.law p n) = ∞ := by
  simp

example : (∫⁻ k, (k : ℝ≥0∞) ∂Binomial.law (PoissonRational.bias 1 2
    (by decide) (by decide)) 2) = 1 := by
  rw [Binomial.mean]
  norm_num [PoissonRational.bias, RationalCoin.bias]
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

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


example (E : CoPset) (x y : ℕ) (hy : 0 < y) (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂ProbabilityTheory.poissonMeasure (PoissonRational.rate x y)) ∗ I -∗
      tglWp E pl(&Occil.poissonRational #int (x : ℤ) #int (y : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (PoissonRational.poissonRational_distSpec E x y hy) F I

example (E : CoPset) (n : ℕ) [NeZero n] (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂UniformInt.law n) ∗ I -∗
      tglWp E pl(&Occil.Weighted.bitmaskRejection #int (n : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (BitmaskRejection.bitmaskRejection_distSpec E n) F I

#print axioms Binomial.thinning
#print axioms Binomial.filling
#print axioms Binomial.reflection
#print axioms Binomial.mean
#print axioms PoissonRational.poissonRational_distSpec
#print axioms PoissonRational.expectation
#print axioms Distributions.poissonMeasure_bind_binomial
#print axioms Distributions.lintegral_poisson_add
#print axioms BitmaskRejection.bitmaskRejection_distSpec
#print axioms BitmaskRejection.expectation
#print axioms UniformRejection.expectation
#print axioms PowerOfTwoCeiling.twp_powerOfTwoCeiling

end

end ExpansionDiscreteAudit
