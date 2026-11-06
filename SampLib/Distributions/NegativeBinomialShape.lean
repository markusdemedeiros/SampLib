import SampLib.Distributions.NegativeBinomialShapeProposal
import SampLib.Distributions.NegativeBinomialShapeRising

/-! # Real-shape negative binomial by rejection from a larger integer shape

The rising-product acceptance cancels the proposal's multichoose coefficient.
Only the success factor remains: acceptance mass is `p^(M-a)`, with no exception
at `p=1` or at an integer target shape.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SampLib.NegativeBinomialShape

noncomputable section

/-- Ratio of ascending-factorial coefficients at the target and proposal shapes. -/
def ratio (a : ℝ) (M n : ℕ) : ℝ := Ring.multichoose a n / Ring.multichoose (M : ℝ) n

theorem ratio_mem (a : ℝ) (ha : 0 < a) (M : ℕ) (hM : 0 < M) (haM : a ≤ M) (n : ℕ) :
    ratio a M n ∈ Icc (0 : ℝ) 1 := by
  have hd := MultichooseSeries.pos (by exact_mod_cast hM : (0 : ℝ) < M) n
  exact ⟨div_nonneg (MultichooseSeries.nonneg ha.le n) hd.le,
    (div_le_one hd).mpr (MultichooseSeries.mono ha.le haM n)⟩

def acceptance (a : ℝ) (ha : 0 < a) (M : ℕ) (hM : 0 < M) (haM : a ≤ M)
    (n : ℕ) : unitInterval := ⟨ratio a M n, ratio_mem a ha M hM haM n⟩

def acceptanceMass (a : ℝ) (p : unitInterval) (M : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((p : ℝ) ^ ((M : ℝ) - a))

theorem acceptanceMass_pos (a : ℝ) (p : unitInterval) (hp : 0 < (p : ℝ)) (M : ℕ) :
    0 < acceptanceMass a p M := ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hp _)

/-- Cancellation uses finite scalar coefficients; continuation credits remain in ENNReal. -/
theorem weighted_pmf (a : ℝ) (ha : 0 < a) (p : unitInterval) (hp : 0 < (p : ℝ))
    (M : ℕ) (hM : 0 < M) (n : ℕ) :
    ENNReal.ofReal (ratio a M n) * pmf (M : ℝ) p n = acceptanceMass a p M * pmf a p n := by
  have hd := MultichooseSeries.pos (by exact_mod_cast hM : (0 : ℝ) < M) n
  have hr : 0 ≤ ratio a M n := div_nonneg (MultichooseSeries.nonneg ha.le n) hd.le
  have hpow : (p : ℝ) ^ ((M : ℝ) - a) * (p : ℝ) ^ a = (p : ℝ) ^ (M : ℝ) := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  have hreal : ratio a M n *
      (Ring.multichoose (M : ℝ) n * (p : ℝ) ^ (M : ℝ) * (1 - (p : ℝ)) ^ n) =
      (p : ℝ) ^ ((M : ℝ) - a) *
        (Ring.multichoose a n * (p : ℝ) ^ a * (1 - (p : ℝ)) ^ n) := by
    unfold ratio
    field_simp [hd.ne']
    rw [← hpow]
    ring
  change ENNReal.ofReal (ratio a M n) * ENNReal.ofReal _ =
    ENNReal.ofReal _ * ENNReal.ofReal _
  rw [← ENNReal.ofReal_mul hr,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg p.2.1 _), hreal]

/-- The accepted part of the actual integer proposal is a scalar times the target law. -/
theorem weighted_expectation (a : ℝ) (ha : 0 < a) (p : unitInterval) (hp : 0 < (p : ℝ))
    (M : ℕ) (hM : 0 < M) (haM : a ≤ M) (F : ℕ → ℝ≥0∞) :
    (∫⁻ n, ENNReal.ofReal (acceptance a ha M hM haM n : ℝ) * F n
      ∂NegativeBinomial.law p M) = acceptanceMass a p M * ∫⁻ n, F n ∂law a ha p hp := by
  rw [integer_law_eq p hp M hM, expectation _ _ p hp, expectation a ha p hp,
    ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro n
  change pmf (M : ℝ) p n * (ENNReal.ofReal (ratio a M n) * F n) =
    acceptanceMass a p M * (pmf a p n * F n)
  calc
    _ = (ENNReal.ofReal (ratio a M n) * pmf (M : ℝ) p n) * F n := by ring
    _ = _ := by rw [weighted_pmf a ha p hp M hM n]; ring

theorem accepted_mass (a : ℝ) (ha : 0 < a) (p : unitInterval) (hp : 0 < (p : ℝ))
    (M : ℕ) (hM : 0 < M) (haM : a ≤ M) :
    AcceptedProposal.mass (NegativeBinomial.law p M) (acceptance a ha M hM haM) =
      acceptanceMass a p M := by
  simpa only [AcceptedProposal.mass, AcceptedProposal.weight, mul_one, lintegral_one,
    measure_univ] using weighted_expectation a ha p hp M hM haM (fun _ => 1)

theorem accepted_mass_ne_zero (a : ℝ) (ha : 0 < a) (p : unitInterval) (hp : 0 < (p : ℝ))
    (M : ℕ) (hM : 0 < M) (haM : a ≤ M) :
    AcceptedProposal.mass (NegativeBinomial.law p M) (acceptance a ha M hM haM) ≠ 0 := by
  rw [accepted_mass a ha p hp M hM haM]
  exact (acceptanceMass_pos a p hp M).ne'

/-- Normalizing the accepted proposal gives exactly the canonical real-shape measure. -/
theorem accepted_law_eq (a : ℝ) (ha : 0 < a) (p : unitInterval) (hp : 0 < (p : ℝ))
    (M : ℕ) (hM : 0 < M) (haM : a ≤ M) :
    AcceptedProposal.law (NegativeBinomial.law p M) (acceptance a ha M hM haM)
      (accepted_mass_ne_zero a ha p hp M hM haM) = law a ha p hp := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [AcceptedProposal.law, lintegral_smul_measure, smul_eq_mul,
    lintegral_withDensity_eq_lintegral_mul _
      (AcceptedProposal.measurable_weight _ (measurable_of_countable _)) hF]
  change (AcceptedProposal.mass (NegativeBinomial.law p M) (acceptance a ha M hM haM))⁻¹ *
    (∫⁻ n, ENNReal.ofReal (acceptance a ha M hM haM n : ℝ) * F n
      ∂NegativeBinomial.law p M) = _
  rw [weighted_expectation a ha p hp M hM haM F, accepted_mass a ha p hp M hM haM,
    ← mul_assoc, ENNReal.inv_mul_cancel (acceptanceMass_pos a p hp M).ne'
      ENNReal.ofReal_ne_top, one_mul]

/-- The standard bounded-amplification rejection kernel preserves all ENNReal credits. -/
theorem conservation (a : ℝ) (ha : 0 < a) (p : unitInterval) (hp : 0 < (p : ℝ))
    (M : ℕ) (hM : 0 < M) (haM : a ≤ M) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ n, AcceptedProposal.kernel (NegativeBinomial.law p M) (acceptance a ha M hM haM)
      (accepted_mass_ne_zero a ha p hp M hM haM) F ε n ∂NegativeBinomial.law p M) ≤
      (∫⁻ n, F n ∂law a ha p hp) + ε := by
  have h := AcceptedProposal.expectation_preservation (NegativeBinomial.law p M)
    (acceptance a ha M hM haM) (measurable_of_countable _)
    (accepted_mass_ne_zero a ha p hp M hM haM) F (measurable_of_countable _) ε
  simpa only [AcceptedProposal.credit, accepted_law_eq a ha p hp M hM haM] using h

end

end SampLib.NegativeBinomialShape
