module

public import SampLib.Common.Laws.ExponentialFactory
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Function.Floor

@[expose] public section

/-! # Exponential masses on dyadic digit cells

On every interval, the upper half receives the same logistic fraction of the
exponential mass, independently of the interval's location. Normalization on
`[0,1)` therefore gives exactly the binary digit probabilities used by the source.
-/

open Set MeasureTheory Real
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.ExponentialDigits

noncomputable section

/-- The unnormalized exponential density, before restricting the fractional part. -/
def density (rate x : ℝ) : ℝ≥0∞ := ofReal (rate * exp (-(rate * x)))

@[fun_prop] theorem measurable_density (rate : ℝ) : Measurable (density rate) := by
  unfold density
  fun_prop

/-- Exponential mass on a finite half-open interval is an antiderivative difference. -/
theorem interval_mass (rate : ℝ) (hrate : 0 < rate) (a b : ℝ) (hab : a ≤ b) :
    (∫⁻ x in Ico a b, density rate x) = ofReal (exp (-(rate * a)) - exp (-(rate * b))) := by
  rw [restrict_Ico_eq_restrict_Icc]
  unfold density
  rw [← ofReal_integral_eq_lintegral_ofReal
      (by fun_prop : Continuous (fun x : ℝ => rate * exp (-(rate * x)))).integrableOn_Icc
      (Filter.Eventually.of_forall (fun x => mul_nonneg hrate.le (exp_pos _).le)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  congr 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => ProbabilityTheory.hasDerivAt_neg_exp_mul_exp (r := rate) (x := x))
    (Continuous.intervalIntegrable (by fun_prop) a b)
  linarith

/-- The mass of the fractional interval is strictly between zero and one. -/
theorem normalizer_pos (rate : ℝ) (hrate : 0 < rate) : 0 < 1 - exp (-rate) := by
  exact sub_pos.mpr (exp_lt_one_iff.mpr (neg_neg_of_pos hrate))

/-- The exponential distribution conditioned to lie in `[0,1)`. -/
def fraction (rate : ℝ) : Measure ℝ :=
  (ofReal (1 - exp (-rate)))⁻¹ •
    (volume.withDensity (density rate)).restrict (Ico 0 1)

theorem fraction_probability (rate : ℝ) (hrate : 0 < rate) :
    IsProbabilityMeasure (fraction rate) where
  measure_univ := by
    rw [fraction, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, withDensity_apply _ measurableSet_Ico, interval_mass rate hrate 0 1
        zero_le_one]
    simp only [mul_zero, neg_zero, exp_zero, mul_one]
    exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr (normalizer_pos rate hrate)))
      ENNReal.ofReal_ne_top

/-- Restriction and normalization preserve Lebesgue null sets, including all endpoints. -/
theorem fraction_absolutelyContinuous (rate : ℝ) : fraction rate ≪ volume := by
  unfold fraction
  exact (Measure.absolutelyContinuous_restrict.trans
    (withDensity_absolutelyContinuous volume (density rate))).smul_left _

instance fraction_noAtoms (rate : ℝ) : NullSingletonClass (fraction rate) where
  measure_singleton x := fraction_absolutelyContinuous rate (measure_singleton x)

/-- Explicit mass of any subinterval of the fractional support. -/
theorem fraction_interval (rate : ℝ) (hrate : 0 < rate) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    fraction rate (Ico a b) = (ofReal (1 - exp (-rate)))⁻¹ *
      ofReal (exp (-(rate * a)) - exp (-(rate * b))) := by
  rw [fraction, Measure.smul_apply, Measure.restrict_apply measurableSet_Ico]
  have hi : Ico a b ∩ Ico 0 1 = Ico a b := by
    apply inter_eq_left.mpr
    intro x hx
    exact ⟨ha.trans hx.1, hx.2.trans_le hb⟩
  rw [hi, withDensity_apply _ measurableSet_Ico, interval_mass rate hrate a b hab]
  rfl

/-- Every nonempty cell inside the unit interval has positive mass. -/
theorem fraction_interval_ne_zero (rate : ℝ) (hrate : 0 < rate) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) : fraction rate (Ico a b) ≠ 0 := by
  rw [fraction_interval rate hrate a b ha hab.le hb]
  apply mul_ne_zero (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
  apply ne_of_gt (ENNReal.ofReal_pos.mpr _)
  apply sub_pos.mpr
  exact exp_lt_exp.mpr (by nlinarith)

/-- The next digit's success probability for a cell of width `width`. -/
def bitBias (rate width : ℝ) : unitInterval :=
  ⟨1 / (1 + exp (rate * width / 2)), by positivity,
    (div_le_one (by positivity)).mpr (by linarith [exp_pos (rate * width / 2)])⟩

/-- A cross-multiplied identity avoids dividing by a possibly tiny interval mass. -/
theorem half_mass (rate a b : ℝ) :
    exp (-(rate * ((a + b) / 2))) - exp (-(rate * b)) =
      (bitBias rate (b - a) : ℝ) * (exp (-(rate * a)) - exp (-(rate * b))) := by
  have hleft : exp (rate * (b - a) / 2) * exp (-(rate * ((a + b) / 2))) =
      exp (-(rate * a)) := by rw [← exp_add]; congr 1; ring
  have hright : exp (rate * (b - a) / 2) * exp (-(rate * b)) =
      exp (-(rate * ((a + b) / 2))) := by rw [← exp_add]; congr 1; ring
  dsimp [bitBias]
  rw [div_mul_eq_mul_div, one_mul]
  apply (eq_div_iff (by positivity : 1 + exp (rate * (b - a) / 2) ≠ 0)).mpr
  nlinarith

/-- The upper half of a cell receives exactly its logistic share of the whole mass. -/
theorem fraction_half (rate : ℝ) (hrate : 0 < rate) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    fraction rate (Ico ((a + b) / 2) b) =
      ofReal (bitBias rate (b - a) : ℝ) * fraction rate (Ico a b) := by
  rw [fraction_interval rate hrate _ b (by linarith) (by linarith) hb,
    fraction_interval rate hrate a b ha hab hb, half_mass,
    ENNReal.ofReal_mul (bitBias rate (b - a)).2.1]
  ring

/-- Conditioning on any reachable cell gives the source's next-bit probability. -/
theorem conditional_half (rate : ℝ) (hrate : 0 < rate) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ProbabilityTheory.cond (fraction rate) (Ico a b) (Ico ((a + b) / 2) b) =
      ofReal (bitBias rate (b - a) : ℝ) := by
  let := fraction_probability rate hrate
  rw [ProbabilityTheory.cond_apply measurableSet_Ico]
  have hi : Ico a b ∩ Ico ((a + b) / 2) b = Ico ((a + b) / 2) b := by
    apply inter_eq_right.mpr
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  rw [hi, fraction_half rate hrate a b ha hab.le hb]
  calc
    _ = ofReal (bitBias rate (b - a) : ℝ) *
        ((fraction rate (Ico a b))⁻¹ * fraction rate (Ico a b)) := by ring
    _ = _ := by
      rw [ENNReal.inv_mul_cancel (fraction_interval_ne_zero rate hrate a b ha hab hb)
        (measure_ne_top _ _), mul_one]

end

end SampLib.ExponentialDigits
