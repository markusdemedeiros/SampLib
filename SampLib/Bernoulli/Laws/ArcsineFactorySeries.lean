module

public import SampLib.Bernoulli.Laws.ArcsineFactoryCoefficients
public import SampLib.Common.Laws.FractionalPower
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! # Central-binomial generating functions for the arcsine factory -/

open Set MeasureTheory
open scoped Topology

namespace SampLib.ArcsineFactorySeries

noncomputable section

open ArcsineFactoryCoefficients

/-- The central-binomial weights are exactly the half-power survival coefficients. -/
theorem weight_eq_survival (n : ℕ) :
    (weight n : ℝ) = FractionalPower.survival (1 / 2) n := by
  induction n with
  | zero => simp [weight]
  | succ n IH =>
    rw [weight_succ, FractionalPower.survival_succ]
    simp only [Rat.cast_mul, Rat.cast_sub, Rat.cast_one, Rat.cast_div, Rat.cast_ofNat,
      Rat.cast_add, Rat.cast_natCast, IH]

/-- The generalized binomial series yields the inverse square root. -/
theorem generating {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun n => (weight n : ℝ) * x ^ n) (1 / Real.sqrt (1 - x)) := by
  have hp : 0 < 1 - x := by linarith
  have h := (FractionalPower.success_hasSum (r := 1 / 2) hp (by linarith)).div_const (1 - x)
  have he : (1 - x) ^ (1 / 2 : ℝ) / (1 - x) = 1 / Real.sqrt (1 - x) := by
    calc
      _ = (1 - x) ^ (1 / 2 : ℝ) / (1 - x) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (1 - x) ^ ((1 / 2 : ℝ) - 1) := (Real.rpow_sub hp _ _).symm
      _ = (1 - x) ^ (-(1 / 2 : ℝ)) := by congr 1; norm_num
      _ = _ := by rw [Real.rpow_neg hp.le, ← Real.sqrt_eq_rpow, one_div]
  rw [he] at h
  convert h using 1
  ext n
  rw [weight_eq_survival]
  have hx : 1 - (1 - x) = x := by ring
  rw [hx]
  field_simp

def value (p : ℝ) : ℝ := Real.arcsin p + Real.sqrt (1 - p ^ 2) - 1

private theorem radical_pos {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) : 0 < 1 - u ^ 2 := by
  nlinarith

/-- Differentiating the target function exposes its central-binomial kernel. -/
theorem derivative {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    HasDerivAt value ((1 - u) / Real.sqrt (1 - u ^ 2)) u := by
  have hs := (((hasDerivAt_const u (1 : ℝ)).sub ((hasDerivAt_id u).pow 2)).sqrt
    (radical_pos hu0 hu1).ne')
  have h := ((Real.hasDerivAt_arcsin (by linarith) (by linarith)).add hs).sub_const 1
  convert h using 1
  · ext x
    simp only [value, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
  · simp only [Pi.sub_apply, Pi.pow_apply, id_eq, mul_one, zero_sub, Nat.cast_ofNat]
    field_simp
    ring

theorem integral_kernel {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ∫ u in (0 : ℝ)..p, (1 - u) / Real.sqrt (1 - u ^ 2) = value p := by
  have hc : ContinuousOn (fun u : ℝ => (1 - u) / Real.sqrt (1 - u ^ 2)) (Icc 0 p) :=
    (continuous_const.sub continuous_id).continuousOn.div
      (Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))).continuousOn
      (fun u hu => (Real.sqrt_pos.mpr (radical_pos hu.1 (hu.2.trans_lt hp1))).ne')
  have hd (u : ℝ) (hu : u ∈ uIcc 0 p) :
      HasDerivAt value ((1 - u) / Real.sqrt (1 - u ^ 2)) u := by
    have hu' : u ∈ Icc 0 p := by simpa only [uIcc_of_le hp0] using hu
    exact derivative hu'.1 (hu'.2.trans_lt hp1)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (ContinuousOn.intervalIntegrable_of_Icc hp0 hc)
  simpa only [value, Real.arcsin_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    sub_zero, Real.sqrt_one, zero_add, sub_self] using h

def term (n : ℕ) (u : ℝ) : ℝ :=
  (weight n : ℝ) * (u ^ (2 * n) - u ^ (2 * n + 1))

private theorem term_bound {p u : ℝ} (hp1 : p < 1) (hu0 : 0 ≤ u) (hup : u ≤ p)
    (n : ℕ) : ‖term n u‖ ≤ p ^ (2 * n) := by
  have hw0 : (0 : ℝ) ≤ weight n := by exact_mod_cast weight_nonneg n
  have hw1 : (weight n : ℝ) ≤ 1 := by exact_mod_cast weight_le_one n
  have hu1 : u ≤ 1 := hup.trans hp1.le
  have hgap : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  have he : term n u = (weight n : ℝ) * (1 - u) * u ^ (2 * n) := by
    unfold term
    rw [pow_succ]
    ring
  rw [he, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (1 : ℝ) * u ^ (2 * n) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hu0 _)
      calc
        _ ≤ 1 * (1 - u) := mul_le_mul_of_nonneg_right hw1 (sub_nonneg.mpr hu1)
        _ ≤ 1 := by linarith
    _ ≤ p ^ (2 * n) := by simpa only [one_mul] using pow_le_pow_left₀ hu0 hup (2 * n)

/-- A geometric majorant justifies integrating the central-binomial series termwise. -/
theorem integrated_series {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    HasSum (fun n => ∫ u in (0 : ℝ)..p, term n u) (value p) := by
  have hsum : Summable (fun n : ℕ => p ^ (2 * n)) := by
    have hp2 : p ^ 2 < 1 := by nlinarith
    simpa only [pow_mul] using summable_geometric_of_lt_one (sq_nonneg p) hp2
  have hs := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := p) (F := term)
    (f := fun u => (1 - u) / Real.sqrt (1 - u ^ 2)) (fun n _ => p ^ (2 * n))
    (fun n => (show Continuous (term n) from by unfold term; fun_prop).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun u hu => by
      have hu' : u ∈ Ioc 0 p := by simpa only [uIoc_of_le hp0] using hu
      exact term_bound hp1 hu'.1.le hu'.2 n)
    (Filter.Eventually.of_forall fun _ _ => hsum)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun u hu => by
      have hu' : u ∈ Ioc 0 p := by simpa only [uIoc_of_le hp0] using hu
      have hu1 := hu'.2.trans_lt hp1
      have h := (generating (sq_nonneg u) (by nlinarith [hu'.1] : u ^ 2 < 1)).mul_left (1 - u)
      convert h using 1
      · ext n
        simp only [term, pow_succ, pow_mul]
        ring
      · ring)
  rw [integral_kernel hp0 hp1] at hs
  exact hs

/-- Each integrated term is the difference of one even and the following odd coefficient. -/
theorem integral_term (p : ℝ) (n : ℕ) :
    ∫ u in (0 : ℝ)..p, term n u = (weight n : ℝ) *
      (p ^ (2 * n + 1) / (2 * n + 1) - p ^ (2 * n + 2) / (2 * n + 2)) := by
  change (∫ u in (0 : ℝ)..p, (weight n : ℝ) *
    (u ^ (2 * n) - u ^ (2 * n + 1))) = _
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    (Continuous.intervalIntegrable (by fun_prop) 0 p)
    (Continuous.intervalIntegrable (by fun_prop) 0 p), integral_pow, integral_pow]
  simp only [zero_pow (by omega : 2 * n + 1 ≠ 0),
    zero_pow (by omega : 2 * n + 1 + 1 ≠ 0), sub_zero, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one]
  congr 1
  ring

end

end SampLib.ArcsineFactorySeries
