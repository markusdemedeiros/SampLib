module

public import SampLib.Bernoulli.Laws.AlternatingPermutationLaw
public import Mathlib.Analysis.Normed.Group.InfiniteSum

@[expose] public section

/-! # The alternating-path generating series

The trigonometric kernel satisfies the same Volterra recurrence as the finite
path probabilities. Their first `N` coefficients differ by at most a constant
times `|p|ᴺ`; separating the series at `p` and `-p` gives secant and tangent.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace SampLib.AlternatingPermutationLaw

noncomputable section

/-- The two reflected solutions of the path-generating Volterra equation. -/
def generatingKernel (p : ℝ) (up : Bool) (x : ℝ) : ℝ :=
  if up then (Real.cos (p * x) + Real.sin (p * (1 - x))) / Real.cos p
  else (Real.cos (p * (1 - x)) + Real.sin (p * x)) / Real.cos p

theorem cos_pos_of_abs_lt_one {p : ℝ} (hp : |p| < 1) : 0 < Real.cos p := by
  apply Real.cos_pos_of_mem_Ioo
  exact ⟨by linarith [(abs_lt.mp hp).1, Real.one_le_pi_div_two],
    by linarith [(abs_lt.mp hp).2, Real.one_le_pi_div_two]⟩

theorem continuous_generatingKernel (p : ℝ) (up : Bool) :
    Continuous (generatingKernel p up) := by
  cases up
  · change Continuous (fun x =>
      (Real.cos (p * (1 - x)) + Real.sin (p * x)) / Real.cos p)
    fun_prop
  · change Continuous (fun x =>
      (Real.cos (p * x) + Real.sin (p * (1 - x))) / Real.cos p)
    fun_prop

private theorem hasDerivAt_generatingKernel (p : ℝ) (up : Bool) (x : ℝ) :
    HasDerivAt (generatingKernel p up)
      ((if up then -p else p) * generatingKernel p (!up) x) x := by
  have hlin := (hasDerivAt_id x).const_mul p
  have href := ((hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id x)).const_mul p
  cases up
  · apply ((href.cos.fun_add hlin.sin).div_const (Real.cos p)).congr_deriv
    simp [generatingKernel]
    ring
  · apply ((hlin.cos.fun_add href.sin).div_const (Real.cos p)).congr_deriv
    simp [generatingKernel]
    ring

/-- The exact first-step identity, valid even at `p = 0`. -/
theorem generatingKernel_recurrence (p : ℝ) (hp : Real.cos p ≠ 0) (up : Bool) (x : ℝ) :
    generatingKernel p up x = 1 + p * transfer (generatingKernel p) up x := by
  cases up
  · have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => hasDerivAt_generatingKernel p false y)
      ((continuous_generatingKernel p true).intervalIntegrable (0 : ℝ) x |>.const_mul p)
    rw [intervalIntegral.integral_const_mul] at h
    simpa [generatingKernel, transfer, hp, sub_eq_iff_eq_add, add_comm] using h.symm
  · have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => hasDerivAt_generatingKernel p true y)
      ((continuous_generatingKernel p false).intervalIntegrable x 1 |>.const_mul (-p))
    rw [intervalIntegral.integral_const_mul] at h
    have hboundary : generatingKernel p true 1 = 1 := by simp [generatingKernel, hp]
    rw [hboundary] at h
    change -p * (∫ y in x..1, generatingKernel p false y) = 1 - generatingKernel p true x at h
    change generatingKernel p true x = 1 + p * (∫ y in x..1, generatingKernel p false y)
    linarith

private theorem generatingKernel_norm_le {p : ℝ} (hp : |p| < 1) (up : Bool) (x : ℝ) :
    ‖generatingKernel p up x‖ ≤ 2 / Real.cos p := by
  have hcos := cos_pos_of_abs_lt_one hp
  cases up <;> dsimp [generatingKernel] <;>
    rw [abs_div, abs_of_pos hcos] <;>
    apply (div_le_div_iff_of_pos_right hcos).mpr
  · exact (abs_add_le _ _).trans (by
      linarith [Real.abs_cos_le_one (p * (1 - x)), Real.abs_sin_le_one (p * x)])
  · exact (abs_add_le _ _).trans (by
      linarith [Real.abs_cos_le_one (p * x), Real.abs_sin_le_one (p * (1 - x))])

private def partialSum (p : ℝ) (N : ℕ) (up : Bool) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, p ^ n * pathMass n up x

private theorem continuous_partialSum (p : ℝ) (N : ℕ) (up : Bool) :
    Continuous (partialSum p N up) := by
  apply continuous_finsetSum
  intro n _
  exact continuous_const.mul (continuous_pathMass n up)

private theorem transfer_partialSum (p : ℝ) (N : ℕ) (up : Bool) (x : ℝ) :
    transfer (partialSum p N) up x =
      ∑ n ∈ Finset.range N, p ^ n * transfer (pathMass n) up x := by
  cases up <;> dsimp [transfer, partialSum]
  · rw [intervalIntegral.integral_finsetSum]
    · simp_rw [intervalIntegral.integral_const_mul]
    · intro n _
      exact ((continuous_pathMass n true).const_mul _).intervalIntegrable _ _
  · rw [intervalIntegral.integral_finsetSum]
    · simp_rw [intervalIntegral.integral_const_mul]
    · intro n _
      exact ((continuous_pathMass n false).const_mul _).intervalIntegrable _ _

private theorem partialSum_succ (p : ℝ) (N : ℕ) (up : Bool) (x : ℝ) :
    partialSum p (N + 1) up x = 1 + p * transfer (partialSum p N) up x := by
  rw [partialSum, Finset.sum_range_succ', transfer_partialSum, Finset.mul_sum]
  simp only [pow_zero, pathMass_zero, one_mul]
  rw [add_comm _ 1]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [pow_succ]
  change p ^ n * p * transfer (pathMass n) up x = p * (p ^ n * transfer (pathMass n) up x)
  ring

private theorem transfer_sub {f g : Bool → ℝ → ℝ}
    (hf : ∀ up, Continuous (f up)) (hg : ∀ up, Continuous (g up)) (up : Bool) (x : ℝ) :
    transfer (fun up x => f up x - g up x) up x = transfer f up x - transfer g up x := by
  cases up <;> dsimp [transfer]
  · exact intervalIntegral.integral_sub ((hf true).intervalIntegrable _ _)
      ((hg true).intervalIntegrable _ _)
  · exact intervalIntegral.integral_sub ((hf false).intervalIntegrable _ _)
      ((hg false).intervalIntegrable _ _)

private theorem error_recurrence (p : ℝ) (hp : Real.cos p ≠ 0) (N : ℕ) (up : Bool) (x : ℝ) :
    generatingKernel p up x - partialSum p (N + 1) up x =
      p * transfer (fun up x => generatingKernel p up x - partialSum p N up x) up x := by
  rw [generatingKernel_recurrence p hp, partialSum_succ,
    transfer_sub (continuous_generatingKernel p) (continuous_partialSum p N)]
  ring

/-- Each additional comparison removes one factor of `|p|` from the unresolved tail. -/
private theorem finite_error {p : ℝ} (hp : |p| < 1) (N : ℕ) (up : Bool) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖generatingKernel p up x - partialSum p N up x‖ ≤ |p| ^ N * (2 / Real.cos p) := by
  have hcos := cos_pos_of_abs_lt_one hp
  induction N generalizing up x with
  | zero => simpa [partialSum] using generatingKernel_norm_le hp up x
  | succ N IH =>
    rw [error_recurrence p hcos.ne', norm_mul, Real.norm_eq_abs]
    calc
      _ ≤ |p| * (|p| ^ N * (2 / Real.cos p)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg p)
        apply transfer_norm_le (by positivity)
        exact fun up x hx => IH up hx
        exact hx
      _ = _ := by rw [pow_succ]; ring

/-- The finite-path generating function is the unique bounded Volterra solution. -/
theorem hasSum_pathMass {p : ℝ} (hp : |p| < 1) (up : Bool) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n => p ^ n * pathMass n up x) (generatingKernel p up x) := by
  have hs : Summable (fun n => p ^ n * pathMass n up x) := by
    apply (summable_geometric_of_lt_one (abs_nonneg p) hp).of_norm_bounded
    intro n
    simpa [norm_mul, norm_pow, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left (pathMass_norm_le_one n up hx) (pow_nonneg (abs_nonneg p) n)
  apply hs.hasSum_iff_tendsto_nat.mpr
  have herr : Tendsto (fun N => generatingKernel p up x - partialSum p N up x)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun N => finite_error hp N up hx)
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg p) hp).mul_const
      (2 / Real.cos p)
  have hc : Tendsto (fun _ : ℕ => generatingKernel p up x) atTop
      (𝓝 (generatingKernel p up x)) := tendsto_const_nhds
  simpa [partialSum] using hc.sub herr

/-- Alternating permutations have generating function `sec p + tan p`. -/
theorem hasSum_eventMass {p : ℝ} (hp : |p| < 1) :
    HasSum (fun n => p ^ n * eventMass n) ((1 + Real.sin p) / Real.cos p) := by
  simpa [eventMass_eq_pathMass_zero, generatingKernel] using
    hasSum_pathMass hp true (x := 0) (by norm_num)

private theorem even_term (p : ℝ) (n : ℕ) :
    (if n % 2 = 0 then p ^ n * eventMass n else 0) =
      (p ^ n * eventMass n + (-p) ^ n * eventMass n) / 2 := by
  by_cases hn : Even n
  · rw [ite_eq_left (Nat.even_iff.mp hn), hn.neg_pow]
    ring
  · have ho : Odd n := Nat.not_even_iff_odd.mp hn
    rw [ite_eq_right (by simpa [← Nat.even_iff] using hn), ho.neg_pow]
    ring

private theorem odd_term (p : ℝ) (n : ℕ) :
    (if n % 2 = 1 then p ^ n * eventMass n else 0) =
      (p ^ n * eventMass n - (-p) ^ n * eventMass n) / 2 := by
  by_cases hn : Even n
  · rw [ite_eq_right (by have := Nat.even_iff.mp hn; omega), hn.neg_pow]
    ring
  · have ho : Odd n := Nat.not_even_iff_odd.mp hn
    rw [ite_eq_left (Nat.not_even_iff.mp hn), ho.neg_pow]
    ring

/-- The even alternating-event volumes have generating function `sec p`. -/
theorem hasSum_even_eventMass {p : ℝ} (hp : |p| < 1) :
    HasSum (fun n => if n % 2 = 0 then p ^ n * eventMass n else 0) (1 / Real.cos p) := by
  have hpos := hasSum_eventMass hp
  have hneg := hasSum_eventMass (p := -p) (by simpa using hp)
  convert (hpos.add hneg).div_const 2 using 1
  · funext n
    exact even_term p n
  · simp only [Real.sin_neg, Real.cos_neg]
    ring

/-- The odd alternating-event volumes have generating function `tan p`. -/
theorem hasSum_odd_eventMass {p : ℝ} (hp : |p| < 1) :
    HasSum (fun n => if n % 2 = 1 then p ^ n * eventMass n else 0) (Real.tan p) := by
  have hpos := hasSum_eventMass hp
  have hneg := hasSum_eventMass (p := -p) (by simpa using hp)
  convert (hpos.sub hneg).div_const 2 using 1
  · funext n
    exact odd_term p n
  · simp only [Real.sin_neg, Real.cos_neg, Real.tan_eq_sin_div_cos]
    ring

/-- Geometric stopping weights the even-event masses by `1-p`. -/
theorem hasSum_even_geometric {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    HasSum (fun n => if n % 2 = 0 then (1 - p) * p ^ n * eventMass n else 0)
      ((1 - p) / Real.cos p) := by
  have h := hasSum_even_eventMass (p := p) (by rwa [abs_of_nonneg hp0])
  convert h.mul_left (1 - p) using 1
  · funext n
    split_ifs <;> simp_all [mul_assoc]
  · ring

/-- Geometric stopping weights the odd-event masses by `1-p`. -/
theorem hasSum_odd_geometric {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    HasSum (fun n => if n % 2 = 1 then (1 - p) * p ^ n * eventMass n else 0)
      ((1 - p) * Real.tan p) := by
  have h := hasSum_odd_eventMass (p := p) (by rwa [abs_of_nonneg hp0])
  convert h.mul_left (1 - p) using 1
  funext n
  split_ifs <;> simp_all [mul_assoc]

end

end SampLib.AlternatingPermutationLaw
