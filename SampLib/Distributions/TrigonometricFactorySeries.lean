module

public import SampLib.Distributions.FactorialSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-! # Coefficient laws for the trigonometric factories

The sinc coefficients decrease precisely on the source range 0 ≤ c ≤ 6.
Their factorial majorant gives summability independently of the input coin.
-/

open Filter
open scoped Topology

namespace SampLib.TrigonometricFactorySeries

noncomputable section

def sincCoefficient (c : ℝ) (n : ℕ) : ℝ := c ^ n / (2 * n + 1).factorial

@[simp] theorem sincCoefficient_zero (c : ℝ) : sincCoefficient c 0 = 1 := by
  simp [sincCoefficient]

theorem sincCoefficient_nonneg {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    0 ≤ sincCoefficient c n := by unfold sincCoefficient; positivity

theorem sincCoefficient_summable {c : ℝ} (hc : 0 ≤ c) :
    Summable (sincCoefficient c) := by
  apply Summable.of_nonneg_of_le (sincCoefficient_nonneg hc) _
    (NormedSpace.expSeries_div_hasSum_exp c).summable
  intro n
  apply div_le_div_of_nonneg_left (pow_nonneg hc n) (by positivity)
  exact_mod_cast Nat.factorial_le (by omega : n ≤ 2 * n + 1)

theorem sincCoefficient_vanishes {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (sincCoefficient c) atTop (𝓝 0) :=
  (sincCoefficient_summable hc).tendsto_atTop_zero

/-- Each successive factorial ratio is at least six. -/
theorem sincCoefficient_antitone {c : ℝ} (hc : 0 ≤ c) (hc6 : c ≤ 6) :
    Antitone (sincCoefficient c) := by
  apply antitone_nat_of_succ_le
  intro n
  have hd : (0 : ℝ) < (2 * n + 1).factorial := by positivity
  have hf : (6 : ℝ) ≤ (2 * (n : ℝ) + 2) * (2 * n + 3) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have he : ((2 * (n + 1) + 1).factorial : ℝ) =
      (2 * n + 1).factorial * ((2 * (n : ℝ) + 2) * (2 * n + 3)) := by
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    ring
  unfold sincCoefficient
  rw [he, pow_succ, div_le_div_iff₀ (mul_pos hd (by positivity)) hd]
  calc
    _ ≤ c ^ n * ((2 * (n : ℝ) + 2) * (2 * n + 3)) * (2 * n + 1).factorial :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hc6.trans hf) (pow_nonneg hc n)) hd.le
    _ = _ := by ring

/-- The cosine factory's power is p, so its analytic argument is sqrt(p). -/
theorem hasSum_cosineSqrt {p : ℝ} (hp : 0 ≤ p) :
    HasSum (fun n => AlternatingEnclosure.sign n * p ^ n *
      FactorialSeries.coefficient .cos n) (Real.cos (Real.sqrt p)) := by
  convert Real.hasSum_cos (Real.sqrt p) using 1
  ext n
  rw [pow_mul, Real.sq_sqrt hp]
  simp only [AlternatingEnclosure.sign_eq, FactorialSeries.coefficient,
    FactorialSeries.denominator, FactorialSeries.degree, div_eq_mul_inv]

private theorem hasSum_sinc (x : ℝ) :
    HasSum (fun n => AlternatingEnclosure.sign n * x ^ (2 * n) /
      (2 * n + 1).factorial) (Real.sinc x) := by
  by_cases hx : x = 0
  · subst x
    have h : (fun n => AlternatingEnclosure.sign n * (0 : ℝ) ^ (2 * n) /
        (2 * n + 1).factorial) = fun n => if n = 0 then 1 else 0 := by
      funext n
      by_cases hn : n = 0
      · subst n
        norm_num [AlternatingEnclosure.sign]
      · have hn' : 2 * n ≠ 0 := by omega
        simp [hn, hn']
    rw [h, Real.sinc_zero]
    exact hasSum_ite_eq 0 1
  · have h := (Real.hasSum_sin x).div_const x
    rw [← Real.sinc_of_ne_zero hx] at h
    convert h using 1
    ext n
    rw [AlternatingEnclosure.sign_eq, pow_succ]
    field_simp

/-- Scaling the coefficient and the input coin multiplies their squared argument. -/
theorem hasSum_sincSqrt {c p : ℝ} (hc : 0 ≤ c) (hp : 0 ≤ p) :
    HasSum (fun n => AlternatingEnclosure.sign n * p ^ n * sincCoefficient c n)
      (Real.sinc (Real.sqrt (c * p))) := by
  convert hasSum_sinc (Real.sqrt (c * p)) using 1
  ext n
  rw [pow_mul, Real.sq_sqrt (mul_nonneg hc hp), mul_pow]
  unfold sincCoefficient
  ring

end

end SampLib.TrigonometricFactorySeries
