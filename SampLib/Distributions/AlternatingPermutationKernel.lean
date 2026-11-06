import SampLib.Distributions.AlternatingPermutationLaw
import SampLib.Distributions.BernoulliMixture
import SampLib.Distributions.BernoulliEndpoints
import SampLib.Distributions.LatentBernoulli

/-! # Continuation-credit kernels for alternating uniform comparisons

The Volterra mass identities identify the success atom of each conditional step.
Bernoulli mixing then transports arbitrary ENNReal continuation credits.
-/

open ProbLang
open LawfulProbLangℝ (unifUnit)
open scoped ENNReal

namespace SampLib.AlternatingPermutationKernel

noncomputable section

open AlternatingPermutationLaw

def pathBias (n : ℕ) (up : Bool) (x : ℝ) : unitInterval :=
  LatentBernoulli.bias (pathMass n up x)

@[simp] theorem pathBias_coe (n : ℕ) (up : Bool) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    (pathBias n up x : ℝ) = pathMass n up x := by
  simp only [pathBias, LatentBernoulli.bias,
    Set.projIcc_of_mem zero_le_one (pathMass_bounds n up hx)]

@[simp] theorem pathBias_zero (up : Bool) (x : ℝ) : pathBias 0 up x = 1 := by
  apply Subtype.ext
  simp only [pathBias, pathMass_zero, LatentBernoulli.bias,
    Set.projIcc_of_mem zero_le_one (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩),
    Set.Icc.coe_one]

theorem measurable_pathBias (n : ℕ) (up : Bool) : Measurable (pathBias n up) :=
  LatentBernoulli.measurable_bias.comp (measurable_pathMass n up)

def nextBias (n : ℕ) (up : Bool) (x y : ℝ) : unitInterval :=
  if up then if x ≤ y then pathBias n false y else 0
  else if y ≤ x then pathBias n true y else 0

def kernel (n : ℕ) (up : Bool) (x : ℝ) (F : Bool → ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  RealCoin.credit (nextBias n up x y) F

def eventBias (n : ℕ) : unitInterval := ⟨eventMass n, eventMass_bounds n⟩

@[simp] theorem eventBias_zero : eventBias 0 = 1 := rfl

section mathematics

open Set MeasureTheory

private theorem measurable_nextBias (n : ℕ) (up : Bool) (x : ℝ) :
    Measurable (nextBias n up x) := by
  cases up
  · change Measurable (fun y => if y ≤ x then pathBias n true y else 0)
    exact Measurable.ite measurableSet_Iic (measurable_pathBias n true) measurable_const
  · change Measurable (fun y => if x ≤ y then pathBias n false y else 0)
    exact Measurable.ite measurableSet_Ici (measurable_pathBias n false) measurable_const

theorem measurable_kernel (n : ℕ) (up : Bool) (x : ℝ) (F : Bool → ℝ≥0∞) :
    Measurable (kernel n up x F) :=
  BernoulliMixture.measurable_credit _ (measurable_nextBias n up x) F

private theorem pathMass_integral (n : ℕ) (up : Bool) (a b : ℝ)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    ∫⁻ y in Icc a b, ENNReal.ofReal (pathMass n up y) =
      ENNReal.ofReal (∫ y in a..b, pathMass n up y) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (continuous_pathMass n up).integrableOn_Icc
    (ae_restrict_of_forall_mem measurableSet_Icc
      (fun y hy => pathMass_nonneg n up ⟨ha.trans hy.1, hy.2.trans hb⟩)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

private theorem success_mass (n : ℕ) (up : Bool) (x : ℝ) (hx : x ∈ Icc 0 1) :
    ∫⁻ y, ENNReal.ofReal (nextBias n up x y : ℝ) ∂unifUnit =
      ENNReal.ofReal (pathBias (n + 1) up x : ℝ) := by
  rw [pathBias_coe n.succ up x hx]
  change (∫⁻ y in Icc (0 : ℝ) 1, ENNReal.ofReal (nextBias n up x y : ℝ)) = _
  cases up
  · have he (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
        ENNReal.ofReal (nextBias n false x y : ℝ) =
          (Iic x).indicator (fun y => ENNReal.ofReal (pathMass n true y)) y := by
      by_cases h : y ≤ x <;> simp [nextBias, h, pathBias_coe n true y hy]
    rw [setLIntegral_congr_fun measurableSet_Icc he, lintegral_indicator measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Iic, ← Ici_inter_Iic, inter_left_comm,
      Iic_inter_Iic, min_eq_left hx.2, Ici_inter_Iic,
      pathMass_integral n true 0 x le_rfl hx.2 hx.1]
    rfl
  · have he (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
        ENNReal.ofReal (nextBias n true x y : ℝ) =
          (Ici x).indicator (fun y => ENNReal.ofReal (pathMass n false y)) y := by
      by_cases h : x ≤ y <;> simp [nextBias, h, pathBias_coe n false y hy]
    rw [setLIntegral_congr_fun measurableSet_Icc he, lintegral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici, ← Ici_inter_Iic, ← inter_assoc,
      Ici_inter_Ici, max_eq_left hx.1, Ici_inter_Iic,
      pathMass_integral n false x 1 hx.1 le_rfl hx.2]
    rfl

/-- Conditioning the next comparison gives exactly the next Volterra probability. -/
theorem expectation (n : ℕ) (up : Bool) (x : ℝ) (hx : x ∈ Icc 0 1)
    (F : Bool → ℝ≥0∞) :
    ∫⁻ y, kernel n up x F y ∂unifUnit = RealCoin.credit (pathBias (n + 1) up x) F :=
  BernoulliMixture.expectation unifUnit (nextBias n up x) (measurable_nextBias n up x)
    (pathBias (n + 1) up x) (success_mass n up x hx) F

/-- The first uniform averages the mass of the remaining comparisons. -/
theorem initial_expectation (n : ℕ) (F : Bool → ℝ≥0∞) :
    ∫⁻ x, RealCoin.credit (pathBias n true x) F ∂unifUnit =
      RealCoin.credit (eventBias (n + 1)) F := by
  apply BernoulliMixture.expectation unifUnit (pathBias n true)
    (measurable_pathBias n true) (eventBias (n + 1)) _ F
  change (∫⁻ x in Icc (0 : ℝ) 1, ENNReal.ofReal (pathBias n true x : ℝ)) =
    ENNReal.ofReal (eventMass (n + 1))
  rw [setLIntegral_congr_fun measurableSet_Icc
    (fun x hx => congrArg ENNReal.ofReal (pathBias_coe n true x hx)),
    pathMass_integral n true 0 1 le_rfl le_rfl zero_le_one]
  rfl

end mathematics

end

end SampLib.AlternatingPermutationKernel
