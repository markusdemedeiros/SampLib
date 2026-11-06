import SampLib.Bernoulli.Laws.AlternatingSeriesContinuity
import SampLib.Bernoulli.Laws.ArcsineFactorySeries

/-! # The arcsine factory's alternating-series law

Pairing an even and an odd coefficient gives the integral of one central-binomial
term. Continuity then extends the interior identity to the deterministic endpoint.
-/

open Filter
open scoped Topology

namespace SampLib.ArcsineFactoryParameters

noncomputable section

open ArcsineFactoryCoefficients ArcsineFactorySeries

def parameters : AlternatingSeries.Parameters where
  coefficient := coefficient
  nonnegative := coefficient_nonneg
  decreasing := coefficient_antitone
  initial := coefficient_zero.le
  vanishes := coefficient_vanishes

def bias (p : unitInterval) : unitInterval := p * AlternatingSeries.meanBias parameters p

private theorem weight_next_divisor (n : ℕ) :
    (weight (n + 1) : ℝ) / (2 * n + 1) = (weight n : ℝ) / (2 * n + 2) := by
  rw [weight_succ]
  push_cast
  field_simp
  ring

def seriesTerm (p : ℝ) (n : ℕ) : ℝ :=
  AlternatingEnclosure.sign n * p ^ n * (coefficient n : ℝ)

private theorem paired_term (p : ℝ) (n : ℕ) :
    p * (seriesTerm p (2 * n) + seriesTerm p (2 * n + 1)) =
      ∫ u in (0 : ℝ)..p, term n u := by
  rw [integral_term]
  unfold seriesTerm
  rw [coefficient_even, coefficient_odd]
  have he : (2 * n) % 2 = 0 := by omega
  have ho : (2 * n + 1) % 2 = 1 := by omega
  simp only [AlternatingEnclosure.sign, he, ho, ite_true, one_ne_zero, ite_false,
    one_mul, neg_one_mul]
  push_cast
  rw [weight_next_divisor]
  simp only [pow_add, pow_mul, pow_one, pow_two]
  ring

private theorem paired_partial (p : ℝ) (N : ℕ) :
    p * ∑ n ∈ Finset.range (2 * N), seriesTerm p n =
      ∑ n ∈ Finset.range N, ∫ u in (0 : ℝ)..p, term n u := by
  induction N with
  | zero => simp
  | succ N IH =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    calc
      _ = p * ∑ n ∈ Finset.range (2 * N), seriesTerm p n +
          p * (seriesTerm p (2 * N) + seriesTerm p (2 * N + 1)) := by ring
      _ = _ := by rw [IH, paired_term]

/-- Integrating the generating function identifies the full interior source series. -/
theorem bias_coe_lt_one (p : unitInterval) (hp : (p : ℝ) < 1) :
    (bias p : ℝ) = value p := by
  have hi : Tendsto (fun N : ℕ => 2 * N + 1) atTop atTop :=
    tendsto_atTop_mono (fun N => by dsimp; omega) tendsto_id
  have hpartial := (AlternatingSeries.weighted_partialSum_tendsto parameters p).comp hi
  have hsource := hpartial.const_mul (p : ℝ)
  have hsum := (integrated_series p.2.1 hp).tendsto_sum_nat.comp
    (tendsto_atTop_mono Nat.le_succ tendsto_id)
  apply tendsto_nhds_unique _ hsum
  convert hsource using 1
  · ext N
    simpa only [Function.comp_apply, AlternatingSeries.value, parameters, seriesTerm,
      show 2 * N + 1 + 1 = 2 * (N + 1) by omega] using (paired_partial (p : ℝ) (N + 1)).symm
  · rfl

private def approach (n : ℕ) : unitInterval :=
  ⟨(n : ℝ) / (n + 1), div_nonneg (Nat.cast_nonneg _) (by positivity),
    (div_le_one (by positivity)).mpr (by linarith)⟩

private theorem approach_lt_one (n : ℕ) : (approach n : ℝ) < 1 := by
  change (n : ℝ) / (n + 1) < 1
  exact (div_lt_one (by positivity)).mpr (lt_add_one _)

private theorem continuous_bias : Continuous (fun p : unitInterval => (bias p : ℝ)) := by
  change Continuous (fun p : unitInterval =>
    (p : ℝ) * (AlternatingSeries.meanBias parameters p : ℝ))
  exact continuous_subtype_val.mul (AlternatingSeries.continuous_meanBias parameters)

/-- The uniform alternating remainder makes the endpoint p=1 a continuity argument. -/
theorem bias_coe (p : unitInterval) :
    (bias p : ℝ) = Real.arcsin p + Real.sqrt (1 - (p : ℝ) ^ 2) - 1 := by
  change (bias p : ℝ) = value p
  by_cases hp : p = 1
  · subst p
    have ht : Tendsto (fun n => (approach n : ℝ)) atTop (𝓝 (1 : ℝ)) :=
      tendsto_natCast_div_add_atTop 1
    have hsub : Tendsto approach atTop (𝓝 (1 : unitInterval)) := tendsto_subtype_rng.mpr ht
    have hb := continuous_bias.continuousAt.tendsto.comp hsub
    have hc : Continuous value := by unfold value; fun_prop
    have hv := (hc.continuousAt.tendsto.comp ht).congr'
      (Filter.Eventually.of_forall fun n =>
        (bias_coe_lt_one (approach n) (approach_lt_one n)).symm)
    exact tendsto_nhds_unique hb hv
  · exact bias_coe_lt_one p (lt_of_le_of_ne p.2.2 (fun h => hp (Subtype.ext h)))

end

end SampLib.ArcsineFactoryParameters
