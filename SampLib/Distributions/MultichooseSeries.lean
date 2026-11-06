module

public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # Generalized negative-binomial coefficients and their generating series -/

open scoped ENNReal

namespace SampLib.MultichooseSeries

noncomputable section

/-- The ascending product gains one factor while its factorial gains `n+1`. -/
theorem step (a : ℝ) (n : ℕ) :
    Ring.multichoose a (n + 1) = Ring.multichoose a n * (a + n) / (n + 1) := by
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a (n + 1)
  rw [ascPochhammer_succ_right] at h
  simp only [Polynomial.smeval_mul, Polynomial.smeval_add, Polynomial.smeval_X,
    Polynomial.smeval_natCast, ← Ring.factorial_nsmul_multichoose_eq_ascPochhammer,
    nsmul_eq_mul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
  apply (eq_div_iff (by positivity : (n : ℝ) + 1 ≠ 0)).mpr
  apply mul_left_cancel₀ (by positivity : (n.factorial : ℝ) ≠ 0)
  nlinarith [h]

theorem nonneg {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : 0 ≤ Ring.multichoose a n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [step]
    exact div_nonneg (mul_nonneg ih (by positivity)) (by positivity)

theorem pos {a : ℝ} (ha : 0 < a) (n : ℕ) : 0 < Ring.multichoose a n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [step]
    exact div_pos (mul_pos ih (by positivity)) (by positivity)

theorem mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    Ring.multichoose a n ≤ Ring.multichoose b n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [step, step]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul ih (add_le_add hab le_rfl) (by positivity) (nonneg (ha.trans hab) n)

/-- The generalized binomial theorem, with no positivity restriction on its exponent. -/
theorem hasSum (a : ℝ) {z : ℝ} (hz : |z| < 1) :
    HasSum (fun n : ℕ => Ring.multichoose a n * z ^ n) (1 / (1 - z) ^ a) := by
  have hx : z ∈ Metric.eball (0 : ℝ) 1 := by
    simpa [Metric.eball, edist_dist, Real.dist_eq, ENNReal.ofReal_lt_one] using hz
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add,
    Ring.multichoose_eq] using
    (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a).hasSum hx

/-- Multiplication by the positive success factor normalizes the whole power series. -/
theorem hasSum_pmf (a : ℝ) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    HasSum (fun n : ℕ => Ring.multichoose a n * p ^ a * (1 - p) ^ n) 1 := by
  have hz : |1 - p| < 1 := by rw [abs_of_nonneg (sub_nonneg.mpr hp1)]; linarith
  have h := hasSum a hz
  rw [sub_sub_cancel] at h
  convert h.mul_left (p ^ a) using 1
  · funext n
    ring
  · simp [(Real.rpow_pos_of_pos hp a).ne']

/-- The same normalization holds in ENNReal, without converting any continuation credit. -/
theorem tsum_pmf {a p : ℝ} (ha : 0 ≤ a) (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑' n : ℕ, ENNReal.ofReal (Ring.multichoose a n * p ^ a * (1 - p) ^ n)) = 1 := by
  have hnonneg n : 0 ≤ Ring.multichoose a n * p ^ a * (1 - p) ^ n :=
    mul_nonneg (mul_nonneg (nonneg ha n) (Real.rpow_nonneg hp.le _))
      (pow_nonneg (sub_nonneg.mpr hp1) _)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg (hasSum_pmf a hp hp1).summable,
    (hasSum_pmf a hp hp1).tsum_eq, ENNReal.ofReal_one]

end

end SampLib.MultichooseSeries
