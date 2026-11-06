import SampLib.Distributions.AlternatingPermutationLawSeries
import SampLib.Distributions.AlternatingPermutationKernel
import SampLib.Distributions.Geometric

/-! # Geometrically stopped alternating-uniform events

A geometric count chooses a finite comparison event. The even and odd Volterra
series identify its mixture probability with the secant and tangent formulas.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SampLib.AlternatingPermutationMixture

noncomputable section

open AlternatingPermutationLaw AlternatingPermutationKernel

def selectBias (odd : Bool) (n : ℕ) : unitInterval :=
  if n % 2 = odd.toNat then eventBias n else 0

@[simp] theorem selectBias_coe (odd : Bool) (n : ℕ) :
    (selectBias odd n : ℝ) = if n % 2 = odd.toNat then eventMass n else 0 := by
  unfold selectBias
  split_ifs <;> rfl

private theorem integrable_selectBias (p : unitInterval) (odd : Bool) :
    Integrable (fun n => (selectBias odd n : ℝ))
      (ProbabilityTheory.geometricMeasure (unitInterval.symm p)) := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
  exact ae_of_all _ fun n => by
    rw [Real.norm_eq_abs, abs_of_nonneg (selectBias odd n).2.1]
    exact (selectBias odd n).2.2

def mean (p : unitInterval) (odd : Bool) : ℝ :=
  ∫ n, (selectBias odd n : ℝ) ∂ProbabilityTheory.geometricMeasure (unitInterval.symm p)

private theorem mean_mem (p : unitInterval) (odd : Bool) : mean p odd ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact integral_nonneg fun n => (selectBias odd n).2.1
  · have h := integral_mono (integrable_selectBias p odd) (integrable_const (1 : ℝ))
      (fun n => (selectBias odd n).2.2)
    simpa [mean, measureReal_def] using h

def bias (p : unitInterval) (odd : Bool) : unitInterval := ⟨mean p odd, mean_mem p odd⟩

/-- Averaging the Bernoulli success atom determines every continuation expectation. -/
theorem expectation (p : unitInterval) (odd : Bool) (F : Bool → ℝ≥0∞) :
    ∫⁻ n, RealCoin.credit (selectBias odd n) F
      ∂ProbabilityTheory.geometricMeasure (unitInterval.symm p) =
      RealCoin.credit (bias p odd) F := by
  apply BernoulliMixture.expectation _ (selectBias odd) (measurable_of_countable _)
    (bias p odd) _ F
  exact (ofReal_integral_eq_lintegral_ofReal (integrable_selectBias p odd)
    (ae_of_all _ fun n => (selectBias odd n).2.1)).symm

/-- The parity-selected event volumes sum to the source's secant/tangent laws. -/
theorem bias_coe (p : unitInterval) (hp : (p : ℝ) < 1) (odd : Bool) :
    (bias p odd : ℝ) =
      if odd then (1 - (p : ℝ)) * Real.tan p else (1 - (p : ℝ)) / Real.cos p := by
  have hne : unitInterval.symm p ≠ 0 := by
    intro h
    have he := congrArg (fun q : unitInterval => (q : ℝ)) h
    simp only [unitInterval.coe_symm_eq, Set.Icc.coe_zero] at he
    linarith
  have hg := ProbabilityTheory.hasSum_integral_geometricMeasure hne
    (integrable_selectBias p odd)
  have ht : HasSum (fun n => if n % 2 = odd.toNat then
      (1 - (p : ℝ)) * p ^ n * eventMass n else 0) (bias p odd : ℝ) := by
    convert hg using 1
    · ext n
      simp only [unitInterval.coe_symm_eq, sub_sub_cancel, smul_eq_mul, selectBias_coe]
      split_ifs <;> simp_all [mul_assoc, mul_comm, mul_left_comm]
    · rfl
  cases odd
  · exact ht.unique (hasSum_even_geometric p.2.1 hp)
  · exact ht.unique (hasSum_odd_geometric p.2.1 hp)

end

end SampLib.AlternatingPermutationMixture
