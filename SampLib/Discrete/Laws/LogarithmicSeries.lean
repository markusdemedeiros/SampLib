import SampLib.Discrete.Laws.Geometric
import SampLib.Bernoulli.Laws.PLogInverse
import SampLib.Common.Laws.AcceptedProposal
import SampLib.Discrete.Laws.BinomialBinary
import SampLib.Uniform.Laws.RationalCoin

/-! # Logarithmic-series sampling by reciprocal rejection

Weighting a geometric proposal by `1/(n+1)` leaves the logarithmic power series.
Its sum supplies both the normalizer and a positive acceptance probability.
-/

open MeasureTheory ProbabilityTheory
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.LogarithmicSeries

noncomputable section

abbrev proposal (p : unitInterval) : Measure ℕ := Geometric.law (unitInterval.symm p)

def acceptance (n : ℕ) : unitInterval := PLogInverse.countBias (n + 1)

theorem acceptance_coe (n : ℕ) : (acceptance n : ℝ) = 1 / (n + 1 : ℝ) := by
  simp [acceptance, PLogInverse.countBias, RationalCoin.bias]

def normalizer (p : unitInterval) : ℝ := -Real.log (1 - (p : ℝ))

theorem normalizer_pos (p : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    0 < normalizer p :=
  neg_pos.mpr (Real.log_neg (by linarith) (by linarith))

private theorem symm_ne_zero (p : unitInterval) (hp1 : (p : ℝ) < 1) :
    unitInterval.symm p ≠ 0 := by
  intro h
  have := congrArg (fun q : unitInterval => (q : ℝ)) h
  simp only [unitInterval.coe_symm_eq, Set.Icc.coe_zero] at this
  linarith

/-- The reciprocal geometric series has the logarithmic normalizing constant. -/
theorem mass_eq (p : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    AcceptedProposal.mass (proposal p) acceptance =
      ofReal (((1 - (p : ℝ)) / p) * normalizer p) := by
  have hs := (Real.hasSum_pow_div_log_of_abs_lt_one
    (show |(p : ℝ)| < 1 by rwa [abs_of_pos hp])).mul_left ((1 - (p : ℝ)) / p)
  rw [AcceptedProposal.mass, proposal, Geometric.law, geometricMeasure_eq (symm_ne_zero p hp1),
    lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  rw [normalizer, ← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg]
  · apply tsum_congr
    intro n
    rw [AcceptedProposal.weight, acceptance_coe,
      ← ENNReal.ofReal_mul (geometricMeasure_nonneg (unitInterval.symm p) n)]
    congr 1
    simp only [unitInterval.coe_symm_eq]
    rw [pow_succ]
    field_simp [ne_of_gt hp]
    ring
  · intro n
    exact mul_nonneg (div_nonneg (by linarith) hp.le)
      (div_nonneg (pow_nonneg p.2.1 _) (by positivity))
  · exact hs.summable

theorem mass_pos (p : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    AcceptedProposal.mass (proposal p) acceptance ≠ 0 := by
  rw [mass_eq p hp hp1]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr
    (mul_pos (div_pos (by linarith) hp) (normalizer_pos p hp hp1)))

/-- The accepted proposal is shifted to the positive integers. -/
def law (p : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) : Measure ℕ :=
  (AcceptedProposal.law (proposal p) acceptance (mass_pos p hp hp1)).map Nat.succ

instance (p : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    IsProbabilityMeasure (law p hp hp1) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

theorem law_zero (p : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    law p hp hp1 {0} = 0 := by
  rw [law, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hpre : Nat.succ ⁻¹' ({0} : Set ℕ) = ∅ := by ext k; simp
  rw [hpre, measure_empty]

/-- The standard logarithmic-series probability at the positive integer `n+1`. -/
theorem law_succ (p : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (n : ℕ) :
    law p hp hp1 {n + 1} = ofReal ((p : ℝ) ^ (n + 1) / ((n + 1) * normalizer p)) := by
  have hm : 0 < ((1 - (p : ℝ)) / p) * normalizer p :=
    mul_pos (div_pos (by linarith) hp) (normalizer_pos p hp hp1)
  rw [law, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hpre : Nat.succ ⁻¹' ({n + 1} : Set ℕ) = {n} := by ext k; simp
  rw [hpre, AcceptedProposal.law, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ (measurableSet_singleton _), lintegral_singleton,
    AcceptedProposal.weight, acceptance_coe, mass_eq p hp hp1,
    proposal, geometricMeasure_singleton (symm_ne_zero p hp1), ← ENNReal.ofReal_inv_of_pos hm,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (n + 1)),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hm.le)]
  congr 1
  simp only [unitInterval.coe_symm_eq]
  rw [pow_succ]
  field_simp [ne_of_gt hp, ne_of_gt (normalizer_pos p hp hp1),
    ne_of_gt (show 0 < 1 - (p : ℝ) by linarith)]
  ring

/-- The map introduces no credit loss, including for infinite continuation credits. -/
theorem expectation (p : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (F : ℕ → ℝ≥0∞) :
    ∫⁻ n, F (n + 1)
      ∂AcceptedProposal.law (proposal p) acceptance (mass_pos p hp hp1) =
      ∫⁻ n, F n ∂law p hp hp1 := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

open MeasureTheory

theorem bias_pos (a b : ℕ) (ha : 0 < a) (hab : a < b) :
    0 < (BinomialBinary.bias a b : ℝ) := by
  rw [BinomialBinary.bias_coe a b (by omega) hab.le]
  exact div_pos (by exact_mod_cast ha) (by exact_mod_cast lt_trans ha hab)

theorem bias_lt_one (a b : ℕ) (ha : 0 < a) (hab : a < b) :
    (BinomialBinary.bias a b : ℝ) < 1 := by
  rw [BinomialBinary.bias_coe a b (by omega) hab.le]
  exact (div_lt_one (by exact_mod_cast lt_trans ha hab)).mpr (by exact_mod_cast hab)

/-- The standard logarithmic-series law at a valid rational parameter. -/
abbrev rationalLaw (a b : ℕ) (ha : 0 < a) (hab : a < b) :=
  law (BinomialBinary.bias a b) (bias_pos a b ha hab) (bias_lt_one a b ha hab)

/-- Accept the positive successor or retain the amplified retry budget. -/
def branchCredit (p : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (n : ℕ) (accepted : Bool) : ℝ≥0∞ :=
  if accepted then F (n + 1) else
    (∫⁻ k, F k ∂law p hp hp1) + AcceptedProposal.factor (proposal p) acceptance * ε

/-- Conditional expectation of the reciprocal acceptance coin. -/
def proposalCredit (p : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  RealCoin.credit (acceptance n) (branchCredit p hp hp1 F ε n)

/-- Reciprocal weighting preserves the logarithmic-series expectation and retry slack. -/
theorem expectation_preservation (p : unitInterval) (hp : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ n, proposalCredit p hp hp1 F ε n ∂proposal p) ≤
      (∫⁻ k, F k ∂law p hp hp1) + ε := by
  have hC : AcceptedProposal.credit (proposal p) acceptance (mass_pos p hp hp1)
      (fun n => F (n + 1)) = ∫⁻ k, F k ∂law p hp hp1 := expectation p hp hp1 F
  simpa only [proposalCredit, branchCredit, RealCoin.credit, RealCoin.pmf,
    ite_true, Bool.false_eq_true, ite_false, AcceptedProposal.kernel,
    AcceptedProposal.weight, AcceptedProposal.rejectedWeight, hC] using
    AcceptedProposal.expectation_preservation (proposal p) acceptance
      (measurable_of_countable _) (mass_pos p hp hp1) (fun n => F (n + 1))
      (measurable_of_countable _) ε

theorem proposal_bias (a b : ℕ) (ha : 0 < a) (hab : a < b) :
    RationalCoin.bias (b - a : ℕ) b (by omega) (by omega) (by omega) =
      unitInterval.symm (BinomialBinary.bias a b) := by
  apply Subtype.ext
  rw [unitInterval.coe_symm_eq, BinomialBinary.bias_coe a b (by omega) hab.le]
  simp only [RationalCoin.bias, Int.cast_natCast, Nat.cast_sub hab.le]
  push_cast
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (lt_trans ha hab).ne'
  field_simp

end

end SampLib.LogarithmicSeries
