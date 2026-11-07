import SampLib.Discrete.Laws.Geometric
import SampLib.Uniform.Laws.RationalCoin
import SampLib.Common.Laws.Logarithmic

/-! # Laws of the logarithmic Bernoulli factory

Conditioning on a positive geometric failure count `n` gives success probability `1/n`. This
module proves that the resulting mixture has the logarithmic bias `p log(1/p)`.
-/

open MeasureTheory ProbabilityTheory
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.PLogInverse

noncomputable section

/-- The logarithmic bias, including its zero value at `p=1`. -/
def bias (p : unitInterval) (hp : 0 < (p : ℝ)) : unitInterval :=
  ⟨(p : ℝ) * Real.log (1 / (p : ℝ)),
    mul_nonneg p.2.1 (Real.log_nonneg (by simpa using (one_le_div hp).mpr p.2.2)), by
      have h := Real.log_le_sub_one_of_pos (one_div_pos.mpr hp)
      have := mul_le_mul_of_nonneg_left h p.2.1
      have hcalc : (p : ℝ) * (1 / (p : ℝ) - 1) = 1 - (p : ℝ) := by
        field_simp
      rw [hcalc] at this
      exact this.trans (sub_le_self _ p.2.1)⟩

/-- A zero count fails; a positive count succeeds with probability `1/n`. -/
def countBias : ℕ → unitInterval
  | 0 => 0
  | n + 1 => RationalCoin.bias 1 (n + 1) (by omega) (by omega) (by omega)

private theorem countBias_succ (n : ℕ) :
    (countBias (n + 1) : ℝ) = 1 / (n + 1 : ℝ) := by
  simp [countBias, RationalCoin.bias]

/-- A zero count pays the false continuation. -/
theorem credit_zero (F : Bool → ℝ≥0∞) :
    RealCoin.credit (countBias 0) F = F false := by
  simp [RealCoin.credit, RealCoin.pmf, countBias]

/-- The geometric mixture of reciprocal counts is the logarithmic power series. -/
theorem success_probability (p : unitInterval) (hp : 0 < (p : ℝ)) :
    ∫⁻ n, ofReal (countBias n : ℝ) ∂Geometric.law p = ofReal (bias p hp : ℝ) := by
  have hpne : p ≠ 0 := by intro h; simp [h] at hp
  have hs := hasSum_geometric_reciprocal_succ hp p.2.2
  rw [Geometric.law, geometricMeasure_eq hpne, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [show countBias 0 = 0 from rfl]
  simp only [Set.Icc.coe_zero, ENNReal.ofReal_zero, mul_zero, zero_add]
  change _ = ofReal ((p : ℝ) * Real.log (1 / (p : ℝ)))
  rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg]
  · apply tsum_congr
    intro n
    rw [countBias_succ, ← ENNReal.ofReal_mul (geometricMeasure_nonneg p (n + 1))]
    congr 1
    ring
  · intro n
    exact mul_nonneg p.2.1 (div_nonneg (pow_nonneg (sub_nonneg.mpr p.2.2) _) (by positivity))
  · exact hs.summable

/-- The output law: a geometric count, then a coin of bias `countBias n`. -/
def law (p : unitInterval) : Measure Bool :=
  (Geometric.law p).bind (fun n => RealCoin.law (countBias n))

instance (p : unitInterval) : IsProbabilityMeasure (law p) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
    simp only [measure_univ, lintegral_const, one_mul]

/-- Identifying the success atom identifies a probability law on Booleans. -/
theorem law_eq (p : unitInterval) (hp : 0 < (p : ℝ)) :
    law p = RealCoin.law (bias p hp) := by
  have ht : law p {true} = RealCoin.law (bias p hp) {true} := by
    rw [law, Measure.bind_apply (measurableSet_singleton true)
      (measurable_of_countable _).aemeasurable]
    simpa [RealCoin.law, RealCoin.pmf] using success_probability p hp
  apply Measure.ext_of_singleton
  intro b
  cases b with
  | true => exact ht
  | false =>
    have hc : ({true} : Set Bool)ᶜ = {false} := by ext b; cases b <;> simp
    rw [← hc, measure_compl (measurableSet_singleton true) (measure_ne_top _ _),
      measure_compl (measurableSet_singleton true) (measure_ne_top _ _),
      measure_univ, measure_univ, ht]

/-- Conditioning on the failure count preserves the logarithmic Bernoulli expectation. -/
theorem expectation_preservation (p : unitInterval) (hp : 0 < (p : ℝ))
    (F : Bool → ℝ≥0∞) :
    ∫⁻ n, RealCoin.credit (countBias n) F ∂Geometric.law p =
      RealCoin.credit (bias p hp) F := by
  rw [← RealCoin.lintegral_law, ← law_eq p hp, law,
    Measure.lintegral_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable F).aemeasurable]
  simp only [RealCoin.lintegral_law]

end

end SampLib.PLogInverse
