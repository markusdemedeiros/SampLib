import SampLib.Distributions.EnvelopeTransport
import SampLib.Distributions.EnvelopeUniform

/-! # Uniform interval masses averaged over the complete shadow history

The reverse-history mean identities lift to nonnegative endpoint masses. Finite
sums and `ofReal` preserve these identities without any finiteness restriction on
the continuation credits later multiplied by those masses.
-/

open Finset MeasureTheory
open scoped ENNReal

namespace SampLib.EnvelopeFactory

noncomputable section

private theorem weighted_ofReal {ι : Type} [Fintype ι] (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) :
    (∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (f i)) = ENNReal.ofReal (mean w f) := by
  rw [mean, ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw i) (hf i))]
  apply sum_congr rfl
  intro i _
  exact (ENNReal.ofReal_mul (hw i)).symm

namespace Coefficients

variable (a : Coefficients)

def average (p : unitInterval) (t : ℕ) (H : a.State t → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ x, a.stateMass p t x * H x

private theorem rowMean_ofReal (p : unitInterval) (t : ℕ)
    (row : Fin (a.degree t + 1) → ℚ) (hr : ∀ k, 0 ≤ row k) :
    (∑ k, BinomialFinite.pmf p (a.degree t) k * ENNReal.ofReal (row k : ℝ)) =
      ENNReal.ofReal (a.rowMean t row p) := by
  rw [rowMean, ENNReal.ofReal_sum_of_nonneg (fun k _ =>
    mul_nonneg bernstein_nonneg (by exact_mod_cast hr k))]
  apply sum_congr rfl
  intro k _
  rw [ENNReal.ofReal_mul bernstein_nonneg]
  simp only [BinomialFinite.pmf, bernstein_apply]

/-- Any conditional history moment lifts to the corresponding Bernstein mean. -/
theorem average_of_conditional (p : unitInterval) (t : ℕ) (H : a.State t → ℝ≥0∞)
    (row : Fin (a.degree t + 1) → ℚ) (hr : ∀ k, 0 ≤ row k)
    (hc : ∀ k, (∑ h, ENNReal.ofReal (a.toScheme.weight t k h) * H (k, h)) =
      ENNReal.ofReal (row k : ℝ)) :
    a.average p t H = ENNReal.ofReal (a.rowMean t row p) := by
  unfold average
  simp only [State, stateMass, Fintype.sum_prod_type]
  calc
    _ = ∑ k, BinomialFinite.pmf p (a.degree t) k *
        ∑ h, ENNReal.ofReal (a.toScheme.weight t k h) * H (k, h) := by
      apply sum_congr rfl
      intro k _
      rw [mul_sum]
      apply sum_congr rfl
      intro h _
      ring
    _ = _ := by simp only [hc]; exact a.rowMean_ofReal p t row hr

theorem lower_moment (p : unitInterval) (t : ℕ) :
    a.average p t (fun x => ENNReal.ofReal (a.toScheme.thresholds t x.1 x.2).1) =
      ENNReal.ofReal (a.lowerMean t p) := by
  apply a.average_of_conditional p t _ (a.lower t) (fun k => (a.bounds t k).1)
  intro k
  rw [weighted_ofReal _ _ (a.toScheme.weight_nonneg t k)
    (fun h => (a.toScheme.thresholds_bounds t k h).1), (a.toScheme.thresholds_mean t k).1]

theorem failure_moment (p : unitInterval) (t : ℕ) :
    a.average p t (fun x => ENNReal.ofReal (1 - (a.toScheme.thresholds t x.1 x.2).2)) =
      ENNReal.ofReal (1 - a.upperMean t p) := by
  have hr : ∀ k, (0 : ℚ) ≤ 1 - a.upper t k := fun k => sub_nonneg.mpr (a.bounds t k).2.2
  have hc : ∀ k, (∑ h, ENNReal.ofReal (a.toScheme.weight t k h) *
      ENNReal.ofReal (1 - (a.toScheme.thresholds t k h).2)) =
        ENNReal.ofReal ((1 - a.upper t k : ℚ) : ℝ) := by
    intro k
    rw [weighted_ofReal _ _ (a.toScheme.weight_nonneg t k)
      (fun h => sub_nonneg.mpr (a.toScheme.thresholds_bounds t k h).2.2)]
    congr 1
    simp only [mean, mul_sub, mul_one, sum_sub_distrib, a.toScheme.weight_sum,
      Rat.cast_sub, Rat.cast_one]
    change 1 - mean (a.toScheme.weight t k)
      (fun h => (a.toScheme.thresholds t k h).2) = _
    rw [(a.toScheme.thresholds_mean t k).2]
  have he := a.average_of_conditional p t
    (fun x => ENNReal.ofReal (1 - (a.toScheme.thresholds t x.1 x.2).2))
    (fun k => 1 - a.upper t k) hr hc
  simpa only [rowMean, upperMean, Rat.cast_sub, Rat.cast_one, mul_sub, mul_one,
    sum_sub_distrib, bernstein.probability] using he

theorem width_moment (p : unitInterval) (t : ℕ) :
    a.average p t (fun x => ENNReal.ofReal
      ((a.toScheme.thresholds t x.1 x.2).2 - (a.toScheme.thresholds t x.1 x.2).1)) =
      ENNReal.ofReal (a.upperMean t p - a.lowerMean t p) := by
  have hr : ∀ k, (0 : ℚ) ≤ a.upper t k - a.lower t k :=
    fun k => sub_nonneg.mpr (a.bounds t k).2.1
  have hc : ∀ k, (∑ h, ENNReal.ofReal (a.toScheme.weight t k h) * ENNReal.ofReal
      ((a.toScheme.thresholds t k h).2 - (a.toScheme.thresholds t k h).1)) =
        ENNReal.ofReal ((a.upper t k - a.lower t k : ℚ) : ℝ) := by
    intro k
    rw [weighted_ofReal _ _ (a.toScheme.weight_nonneg t k)
      (fun h => sub_nonneg.mpr (a.toScheme.thresholds_bounds t k h).2.1)]
    congr 1
    simp only [mean, mul_sub, sum_sub_distrib, Rat.cast_sub]
    change mean _ (fun h => (a.toScheme.thresholds t k h).2) -
      mean _ (fun h => (a.toScheme.thresholds t k h).1) = _
    rw [(a.toScheme.thresholds_mean t k).1, (a.toScheme.thresholds_mean t k).2]
  have he := a.average_of_conditional p t
    (fun x => ENNReal.ofReal
      ((a.toScheme.thresholds t x.1 x.2).2 - (a.toScheme.thresholds t x.1 x.2).1))
    (fun k => a.upper t k - a.lower t k) hr hc
  simpa only [rowMean, upperMean, lowerMean, Rat.cast_sub, mul_sub, sum_sub_distrib] using he

end Coefficients

end

end SampLib.EnvelopeFactory
