import SampLib.Bernoulli.Laws.AlternatingSeriesMean
import SampLib.Bernoulli.Laws.ShiftedExponential
import SampLib.Bernoulli.Laws.ReciprocalAffine
import SampLib.Bernoulli.Laws.CoinConditional

/-! # The continuous extension of `(1-exp(-x))/x` -/

open Filter
open scoped ENNReal Topology

namespace SampLib.ExpIntegral

noncomputable section

def value (x : ℝ) : ℝ := if x = 0 then 1 else (1 - Real.exp (-x)) / x

def parameters : AlternatingSeries.Parameters where
  coefficient n := 1 / ((n + 1).factorial : ℚ)
  nonnegative n := by positivity
  decreasing := by
    intro i j hij
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.factorial_le (Nat.add_le_add_right hij 1)
  initial := by norm_num
  vanishes := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Function.comp_def] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (factorial_tendsto_atTop.comp (tendsto_atTop_mono Nat.le_succ tendsto_id))

/-- Removing the constant exponential term and dividing by `-p` gives the factorial integral. -/
theorem hasSum (p : ℝ) :
    HasSum (fun n => AlternatingEnclosure.sign n * p ^ n *
      AlternatingSeries.value parameters n) (value p) := by
  by_cases hp : p = 0
  · subst p
    have hf : (fun n => AlternatingEnclosure.sign n * (0 : ℝ) ^ n *
        AlternatingSeries.value parameters n) = fun n => if n = 0 then 1 else 0 := by
      funext n
      by_cases hn : n = 0 <;>
        simp [hn, parameters, AlternatingSeries.value, AlternatingEnclosure.sign_eq]
    rw [hf]
    simpa [value] using hasSum_ite_eq 0 (1 : ℝ)
  · have he : HasSum (fun n : ℕ => (-p) ^ n / n.factorial) (Real.exp (-p)) := by
      simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (-p)
    have ht : HasSum (fun n : ℕ => (-p) ^ (n + 1) / (n + 1).factorial)
        (Real.exp (-p) - 1) := by
      simpa using (hasSum_nat_add_iff' 1).2 he
    convert ht.mul_left (-p)⁻¹ using 1
    · funext n
      simp only [AlternatingSeries.value, parameters, AlternatingEnclosure.sign_eq,
        Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
      rw [neg_pow p (n + 1)]
      simp only [pow_succ]
      field_simp
    · simp only [value, ite_eq_right hp]
      field_simp
      ring

theorem zero_bias_coe (p : unitInterval) :
    (AlternatingSeries.meanBias parameters p : ℝ) = value p :=
  AlternatingSeries.mean_eq_of_hasSum parameters p _ (hasSum p)

abbrev reciprocal (p : unitInterval) (m : ℕ) (hm : 0 < m) : unitInterval :=
  ReciprocalAffine.bias p m 1 1 hm hm

abbrev shifted (p : unitInterval) (m : ℕ) : unitInterval :=
  ShiftedExponential.bias p m 1 (Int.natCast_nonneg _) (by decide)

abbrev positiveBias (p : unitInterval) (m : ℕ) (hm : 0 < m) : unitInterval :=
  CoinConditional.bias 0 (reciprocal p m hm) (shifted p m)

def firstCredit (p : unitInterval) (m : ℕ) (hm : 0 < m)
    (F : Bool → ℝ≥0∞) (r : Bool) : ℝ≥0∞ :=
  if r then F false else ∫⁻ b, F b ∂RealCoin.law (reciprocal p m hm)

/-- A failed shifted exponential selects the reciprocal-affine component. -/
theorem expectation_positive (p : unitInterval) (m : ℕ) (hm : 0 < m)
    (F : Bool → ℝ≥0∞) :
    (∫⁻ r, firstCredit p m hm F r ∂RealCoin.law (shifted p m)) =
      ∫⁻ r, F r ∂RealCoin.law (positiveBias p m hm) := by
  simpa [firstCredit, CoinConditional.firstCredit, RealCoin.lintegral_law,
    RealCoin.credit, RealCoin.pmf] using
    CoinConditional.expectation_preservation 0 (reciprocal p m hm) (shifted p m) F

theorem positive_bias_coe (p : unitInterval) (m : ℕ) (hm : 0 < m) :
    (positiveBias p m hm : ℝ) = value ((m : ℝ) + p) := by
  have hx : 0 < (m : ℝ) + p :=
    add_pos_of_pos_of_nonneg (by exact_mod_cast hm) p.2.1
  simp only [value, ite_eq_right hx.ne', positiveBias, CoinConditional.bias, Set.Icc.convexComb,
    Set.Icc.coe_zero, reciprocal, ReciprocalAffine.bias, shifted, ShiftedExponential.bias,
    Int.cast_natCast, Int.cast_one, Nat.cast_one, div_one, one_mul, mul_zero, add_zero]
  ring

def bias (p : unitInterval) (m : ℕ) : unitInterval :=
  if hm : m = 0 then AlternatingSeries.meanBias parameters p
  else positiveBias p m (Nat.pos_of_ne_zero hm)

theorem bias_zero (p : unitInterval) :
    bias p 0 = AlternatingSeries.meanBias parameters p := by simp [bias]

theorem bias_coe (p : unitInterval) (m : ℕ) : (bias p m : ℝ) = value ((m : ℝ) + p) := by
  by_cases hm : m = 0
  · subst m
    simpa [bias] using zero_bias_coe p
  · simpa only [bias, dite_eq_right hm] using positive_bias_coe p m (Nat.pos_of_ne_zero hm)

end

end SampLib.ExpIntegral
