module

public import SampLib.Distributions.FactorialSeries
public import SampLib.Distributions.GeometricThreshold
public import Mathlib.Probability.Distributions.Geometric

@[expose] public section

/-! Averaging first-failure truncations identifies the three factorial-series laws. -/

open MeasureTheory ProbabilityTheory

namespace SampLib.FactorialSeries

noncomputable section

private theorem signed_summable (m : Mode) :
    Summable (fun n => ‖AlternatingEnclosure.sign n * coefficient m n‖) := by
  convert coefficient_summable m using 1
  ext n
  have hs : ‖AlternatingEnclosure.sign n‖ = 1 := by
    unfold AlternatingEnclosure.sign
    split_ifs <;> norm_num
  rw [norm_mul, hs, one_mul, Real.norm_eq_abs, abs_of_nonneg (coefficient_nonneg m n)]

private theorem callback_eq_one (m : Mode) (p : unitInterval)
    (h : callbackBias m p = 1) : p = 1 := by
  apply Subtype.ext
  have he := congrArg (fun q : unitInterval => (q : ℝ)) h
  cases m <;> simp only [callbackBias, Set.Icc.coe_mul, Set.Icc.coe_one] at he ⊢
  · exact he
  · nlinarith [p.2.1, p.2.2]
  · nlinarith [p.2.1, p.2.2]

/-- Geometric averaging weights the nth factorial coefficient by the nth callback power. -/
theorem mean_eq_value (m : Mode) (p : unitInterval) :
    GeometricThreshold.mean (callbackBias m p) (partialBias m) (limitBias m) 0 =
      value m p := by
  by_cases hq : callbackBias m p = 1
  · have hp := callback_eq_one m p hq
    subst p
    rw [hq, GeometricThreshold.mean_one]
    change limit m = value m 1
    simpa [limit, hq] using (hasSum_value m (1 : unitInterval)).tsum_eq
  · let q := callbackBias m p
    have hq1 : (q : ℝ) < 1 := lt_of_le_of_ne q.2.2 (by
      intro he
      exact hq (Subtype.ext he))
    have hsymm : unitInterval.symm q ≠ 0 := by
      intro h
      have := congrArg (fun a : unitInterval => (a : ℝ)) h
      simp only [unitInterval.coe_symm_eq, Set.Icc.coe_zero] at this
      linarith
    have hs := geometric_partial_expectation
      (fun n => AlternatingEnclosure.sign n * coefficient m n)
      (signed_summable m) q q.2.1 hq1
    have hv : HasSum (fun n => (q : ℝ) ^ n *
        (AlternatingEnclosure.sign n * coefficient m n)) (value m p) := by
      convert hasSum_value m p using 1
      ext n
      ring
    rw [GeometricThreshold.mean_of_lt_one _ hq,
      integral_geometricMeasure hsymm]
    calc
      _ = ∑' n, (1 - (q : ℝ)) * q ^ n *
          ∑ j ∈ Finset.range (n + 1), AlternatingEnclosure.sign j * coefficient m j := by
        apply tsum_congr
        intro n
        simp only [unitInterval.coe_symm_eq, zero_add, smul_eq_mul,
          partialBias, partialSum, AlternatingEnclosure.partialSum]
        ring
      _ = _ := hs.tsum_eq.trans hv.tsum_eq

theorem value_mem (m : Mode) (p : unitInterval) : value m p ∈ Set.Icc (0 : ℝ) 1 := by
  rw [← mean_eq_value m p]
  exact GeometricThreshold.mean_mem _ _ _ _

end

end SampLib.FactorialSeries
