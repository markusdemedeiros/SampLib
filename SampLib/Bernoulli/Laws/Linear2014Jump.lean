import SampLib.Common.Laws.Geometric
import SampLib.Common.Laws.BernoulliMixture
import SampLib.Continuous.Laws.IterateCoin
import SampLib.Bernoulli.Laws.CoinConditional

/-! # Geometric jumps in the expanding linear factory

The geometric generating function identifies the harmonic probability `t^state`.
Its verification uses `(1-q)t=p` rather than division by `t`, retaining the
zero-input endpoint and arbitrary infinite continuation credits.
-/

open MeasureTheory ProbabilityTheory
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.Linear2014Jump

noncomputable section

private theorem denominator_pos (q t : unitInterval) (hq : 0 < (q : ℝ)) :
    0 < 1 - (1 - (q : ℝ)) * t := by
  have h := mul_le_of_le_one_right (sub_nonneg.mpr q.2.2) t.2.2
  linarith

/-- The geometric probability-generating function, including `t=0` and `t=1`. -/
def pgfBias (q : unitInterval) (hq : 0 < (q : ℝ)) (t : unitInterval) : unitInterval :=
  ⟨(q : ℝ) / (1 - (1 - (q : ℝ)) * t), div_nonneg q.2.1 (denominator_pos q t hq).le, by
    apply (div_le_one (denominator_pos q t hq)).mpr
    have h := mul_le_of_le_one_right (sub_nonneg.mpr q.2.2) t.2.2
    linarith⟩

private theorem geometric_series (q t : unitInterval) (hq : 0 < (q : ℝ)) :
    HasSum (fun n : ℕ => (1 - (q : ℝ)) ^ n * q * (t : ℝ) ^ n)
      (pgfBias q hq t : ℝ) := by
  have hnonneg : 0 ≤ (1 - (q : ℝ)) * t := mul_nonneg (sub_nonneg.mpr q.2.2) t.2.1
  have hlt : (1 - (q : ℝ)) * t < 1 := by linarith [denominator_pos q t hq]
  convert (hasSum_geometric_of_lt_one hnonneg hlt).mul_right (q : ℝ) using 1
  · ext n
    rw [mul_pow]
    ring
  · dsimp [pgfBias]
    ring

/-- Exact generating-function expectation under the actual geometric law. -/
theorem geometric_pgf (q : unitInterval) (hq : 0 < (q : ℝ)) (t : unitInterval) :
    (∫⁻ n, ofReal ((t : ℝ) ^ n) ∂geometricMeasure q) = ofReal (pgfBias q hq t : ℝ) := by
  have hqne : q ≠ 0 := by intro h; simp [h] at hq
  rw [geometricMeasure_eq hqne]
  simp only [lintegral_sum_measure, lintegral_smul_measure, lintegral_dirac,
    smul_eq_mul]
  simp_rw [← ENNReal.ofReal_mul (geometricMeasure_nonneg q _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg (geometricMeasure_nonneg q n) (pow_nonneg t.2.1 _))
    (geometric_series q t hq).summable, (geometric_series q t hq).tsum_eq]

/-- Average continuation bias after a false input trial and its independent geometric jump. -/
def futureBias (q : unitInterval) (hq : 0 < (q : ℝ)) (t : unitInterval) (s : ℕ) :
    unitInterval := IterateCoin.bias t s * pgfBias q hq t

/-- Geometric averaging preserves all Boolean continuation credits. -/
theorem geometric_expectation (q : unitInterval) (hq : 0 < (q : ℝ)) (t : unitInterval)
    (s : ℕ) (F : Bool → ℝ≥0∞) :
    (∫⁻ n, IterateCoin.credit t (s + n) F ∂geometricMeasure q) =
      RealCoin.credit (futureBias q hq t s) F := by
  apply BernoulliMixture.expectation _ _ (measurable_of_countable _)
  change (∫⁻ n, ofReal ((t : ℝ) ^ (s + n)) ∂geometricMeasure q) =
    ofReal ((t : ℝ) ^ s * (pgfBias q hq t : ℝ))
  simp_rw [pow_add, ENNReal.ofReal_mul (pow_nonneg t.2.1 s)]
  rw [lintegral_const_mul _ (measurable_of_countable _), geometric_pgf]

private theorem harmonic (p q t : unitInterval) (hq : 0 < (q : ℝ))
    (hrelation : (1 - (q : ℝ)) * t = p) (s : ℕ) (hs : 0 < s) :
    CoinConditional.bias (IterateCoin.bias t (s - 1)) (futureBias q hq t s) p =
      IterateCoin.bias t s := by
  apply Subtype.ext
  have hpow : (t : ℝ) ^ s = (t : ℝ) ^ (s - 1) * t := by
    rw [← pow_succ, Nat.sub_add_cancel hs]
  change (1 - (p : ℝ)) * ((t : ℝ) ^ s *
    ((q : ℝ) / (1 - (1 - (q : ℝ)) * t))) + p * (t : ℝ) ^ (s - 1) = (t : ℝ) ^ s
  rw [← hrelation, hpow]
  field_simp [(denominator_pos q t hq).ne']
  ring

def inputCredit (q : unitInterval) (t : unitInterval) (s : ℕ)
    (F : Bool → ℝ≥0∞) (a : Bool) : ℝ≥0∞ :=
  if a then IterateCoin.credit t (s - 1) F
  else ∫⁻ n, IterateCoin.credit t (s + n) F ∂geometricMeasure q

/-- One input trial and its possible geometric jump preserve `t^state` credits. -/
theorem jump_expectation (p q t : unitInterval) (hq : 0 < (q : ℝ))
    (hrelation : (1 - (q : ℝ)) * t = p) (s : ℕ) (hs : 0 < s) (F : Bool → ℝ≥0∞) :
    (∫⁻ a, inputCredit q t s F a ∂RealCoin.law p) = IterateCoin.credit t s F := by
  have h := CoinConditional.expectation_preservation
    (IterateCoin.bias t (s - 1)) (futureBias q hq t s) p F
  have hcredit : inputCredit q t s F =
      CoinConditional.firstCredit (IterateCoin.bias t (s - 1)) (futureBias q hq t s) F := by
    funext a
    cases a
    · simpa only [inputCredit, CoinConditional.firstCredit, Bool.false_eq_true, ite_false,
        RealCoin.lintegral_law] using geometric_expectation q hq t s F
    · simp only [inputCredit, CoinConditional.firstCredit, ite_true,
        RealCoin.lintegral_law, IterateCoin.credit]
  rw [hcredit]
  simpa only [CoinConditional.law, RealCoin.lintegral_law, IterateCoin.credit,
    harmonic p q t hq hrelation s hs] using h

end

end SampLib.Linear2014Jump
