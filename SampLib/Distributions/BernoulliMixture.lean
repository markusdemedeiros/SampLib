import SampLib.Samplers.RealCoin

/-! # Identifying mixtures of Bernoulli laws

A probability measure on Booleans is determined by its success atom. Applying
this before integrating continuation credits avoids subtracting infinite values.
-/

open MeasureTheory
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.BernoulliMixture

noncomputable section

/-- Bernoulli laws vary measurably with their bias. -/
theorem measurable_law : Measurable RealCoin.law := by
  unfold RealCoin.law RealCoin.pmf
  simp only [ite_true, Bool.false_eq_true, ite_false]
  fun_prop

/-- Arbitrary Boolean credits give a measurable conditional-expectation kernel. -/
theorem measurable_credit {α : Type _} [MeasurableSpace α] (φ : α → unitInterval)
    (hφ : Measurable φ) (F : Bool → ℝ≥0∞) :
    Measurable (fun x => RealCoin.credit (φ x) F) := by
  unfold RealCoin.credit RealCoin.pmf
  simp only [ite_true, Bool.false_eq_true, ite_false]
  fun_prop

/-- Normalization and the success probability determine the entire Boolean law. -/
theorem eq_bernoulli_of_apply_true (μ : Measure Bool) [IsProbabilityMeasure μ]
    (p : unitInterval) (hp : μ {true} = ofReal (p : ℝ)) : μ = RealCoin.law p := by
  have ht : μ {true} = RealCoin.law p {true} := by
    simpa [RealCoin.law, RealCoin.pmf] using hp
  apply Measure.ext_of_singleton
  intro b
  cases b with
  | true => exact ht
  | false =>
    have hc : ({true} : Set Bool)ᶜ = {false} := by ext b; cases b <;> simp
    rw [← hc, measure_compl (measurableSet_singleton true) (measure_ne_top _ _),
      measure_compl (measurableSet_singleton true) (measure_ne_top _ _),
      measure_univ, measure_univ, ht]

/-- Averaging the success biases identifies the expectation for all ENNReal credits. -/
theorem expectation {α : Type _} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (φ : α → unitInterval) (hφ : Measurable φ)
    (p : unitInterval) (hp : ∫⁻ x, ofReal (φ x : ℝ) ∂μ = ofReal (p : ℝ))
    (F : Bool → ℝ≥0∞) :
    ∫⁻ x, RealCoin.credit (φ x) F ∂μ = RealCoin.credit p F := by
  let ν := μ.bind (fun x => RealCoin.law (φ x))
  have hκ : Measurable (fun x => RealCoin.law (φ x)) := measurable_law.comp hφ
  let : IsProbabilityMeasure ν := ⟨by
    dsimp only [ν]
    rw [Measure.bind_apply MeasurableSet.univ hκ.aemeasurable]
    simp only [measure_univ, lintegral_const, one_mul]⟩
  have hν : ν = RealCoin.law p := by
    apply eq_bernoulli_of_apply_true
    dsimp only [ν]
    rw [Measure.bind_apply (measurableSet_singleton true) hκ.aemeasurable]
    simpa [RealCoin.law, RealCoin.pmf] using hp
  calc
    _ = ∫⁻ b, F b ∂ν := by
      dsimp only [ν]
      rw [Measure.lintegral_bind hκ.aemeasurable
        (measurable_of_countable F).aemeasurable]
      simp only [RealCoin.lintegral_law]
    _ = _ := by rw [hν, RealCoin.lintegral_law]

end

end SampLib.BernoulliMixture
