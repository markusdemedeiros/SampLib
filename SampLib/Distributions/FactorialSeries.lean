module

public import SampLib.Distributions.AlternatingEnclosure
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

@[expose] public section

/-! # Factorial series used by the lazy Bernoulli factories -/

open Finset Filter
open scoped Topology

namespace SampLib.FactorialSeries

noncomputable section

inductive Mode where
  | exp | cos | sinc
  deriving DecidableEq

def Mode.code : Mode → ℤ
  | .exp => 0
  | .cos => 1
  | .sinc => 2

def degree : Mode → ℕ → ℕ
  | .exp, n => n
  | .cos, n => 2 * n
  | .sinc, n => 2 * n + 1

def denominator (m : Mode) (n : ℕ) : ℕ := (degree m n).factorial

def factor : Mode → ℕ → ℕ
  | .exp, n => n + 1
  | .cos, n => (2 * n + 1) * (2 * n + 2)
  | .sinc, n => (2 * n + 2) * (2 * n + 3)

@[simp] theorem denominator_zero (m : Mode) : denominator m 0 = 1 := by cases m <;> rfl

theorem denominator_pos (m : Mode) (n : ℕ) : 0 < denominator m n := Nat.factorial_pos _

theorem factor_pos (m : Mode) (n : ℕ) : 0 < factor m n := by cases m <;> simp [factor]

theorem denominator_succ (m : Mode) (n : ℕ) :
    denominator m (n + 1) = denominator m n * factor m n := by
  cases m with
  | exp => simp [denominator, degree, factor, Nat.factorial_succ, Nat.mul_comm]
  | cos =>
    simp only [denominator, degree, factor,
      show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    rw [Nat.factorial_succ, Nat.factorial_succ]
    ring
  | sinc =>
    simp only [denominator, degree, factor,
      show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega]
    rw [Nat.factorial_succ, Nat.factorial_succ]
    ring

theorem degree_strictMono (m : Mode) : StrictMono (degree m) := by
  cases m <;> intro i j hij <;> simp only [degree] <;> omega

/-- Positive, decreasing factorial coefficients, with initial coefficient one. -/
def coefficient (m : Mode) (n : ℕ) : ℝ := (denominator m n : ℝ)⁻¹

@[simp] theorem coefficient_zero (m : Mode) : coefficient m 0 = 1 := by simp [coefficient]

theorem coefficient_nonneg (m : Mode) (n : ℕ) : 0 ≤ coefficient m n := by
  unfold coefficient
  positivity

theorem coefficient_anti (m : Mode) : Antitone (coefficient m) := by
  intro i j hij
  unfold coefficient
  apply inv_anti₀ (by exact_mod_cast denominator_pos m i)
  exact_mod_cast Nat.factorial_le ((degree_strictMono m).monotone hij)

theorem coefficient_summable (m : Mode) : Summable (coefficient m) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (1 : ℝ)).summable.comp_injective
    (degree_strictMono m).injective
  convert h using 1
  ext n
  simp only [coefficient, denominator, one_pow, one_div, Function.comp_apply]

/-- Exact partial sums before a failed callback freezes the series. -/
def partialSum (m : Mode) (n : ℕ) : ℝ :=
  AlternatingEnclosure.partialSum (coefficient m) n

def limit (m : Mode) : ℝ := ∑' n, AlternatingEnclosure.sign n * coefficient m n

def lower (m : Mode) := AlternatingEnclosure.lower (coefficient m)

def upper (m : Mode) := AlternatingEnclosure.upper (coefficient m)

theorem partialSum_mem (m : Mode) (n : ℕ) : partialSum m n ∈ Set.Icc (0 : ℝ) 1 := by
  have h := AlternatingEnclosure.future_mem (coefficient m) (coefficient_anti m)
    (coefficient_nonneg m) 0 n (Nat.zero_le _)
  simpa only [partialSum, AlternatingEnclosure.lower_zero, AlternatingEnclosure.upper_zero,
    coefficient_zero, Set.mem_Icc] using h

theorem limit_mem (m : Mode) : limit m ∈ Set.Icc (0 : ℝ) 1 := by
  have h := AlternatingEnclosure.limit_mem (coefficient m) (coefficient_anti m)
    (coefficient_nonneg m) (coefficient_summable m) 0
  simpa only [limit, AlternatingEnclosure.lower_zero, AlternatingEnclosure.upper_zero,
    coefficient_zero, Set.mem_Icc] using h

def partialBias (m : Mode) (n : ℕ) : unitInterval := ⟨partialSum m n, partialSum_mem m n⟩

def limitBias (m : Mode) : unitInterval := ⟨limit m, limit_mem m⟩

/-- The callback group has one success for exp, and two successes for cos and sinc. -/
def callbackBias : Mode → unitInterval → unitInterval
  | .exp, p => p
  | .cos, p => p * p
  | .sinc, p => p * p

def value : Mode → ℝ → ℝ
  | .exp, p => Real.exp (-p)
  | .cos, p => Real.cos p
  | .sinc, p => Real.sinc p

private theorem square_pow (p : unitInterval) (n : ℕ) :
    ((p * p : unitInterval) : ℝ) ^ n = (p : ℝ) ^ (2 * n) := by
  change ((p : ℝ) * p) ^ n = (p : ℝ) ^ (2 * n)
  rw [← pow_two, ← pow_mul]

/-- The three familiar power series identify the weighted factorial coefficients. -/
theorem hasSum_value (m : Mode) (p : unitInterval) :
    HasSum (fun n => AlternatingEnclosure.sign n * (callbackBias m p : ℝ) ^ n *
      coefficient m n) (value m p) := by
  cases m with
  | exp =>
    have h : HasSum (fun n : ℕ => (-(p : ℝ)) ^ n / n.factorial)
        (Real.exp (-(p : ℝ))) := by
      simpa only [← Real.exp_eq_exp_ℝ] using
        NormedSpace.expSeries_div_hasSum_exp (-(p : ℝ))
    convert h using 1
    · ext n
      rw [neg_eq_neg_one_mul, mul_pow]
      simp only [callbackBias, coefficient, denominator, degree,
        AlternatingEnclosure.sign_eq, div_eq_mul_inv]
    · rfl
  | cos =>
    convert Real.hasSum_cos (p : ℝ) using 1
    · ext n
      simp only [callbackBias, square_pow, coefficient, denominator, degree,
        AlternatingEnclosure.sign_eq, div_eq_mul_inv]
    · rfl
  | sinc =>
    by_cases hp : (p : ℝ) = 0
    · have h : (fun n => AlternatingEnclosure.sign n * (callbackBias .sinc p : ℝ) ^ n *
          coefficient .sinc n) = fun n => if n = 0 then (1 : ℝ) else 0 := by
        funext n
        by_cases hn : n = 0
        · subst n; simp [callbackBias, coefficient, denominator, degree, AlternatingEnclosure.sign]
        · simp [callbackBias, hp, hn]
      rw [h]
      simpa only [value, hp, Real.sinc_zero] using hasSum_ite_eq 0 (1 : ℝ)
    · have h := (Real.hasSum_sin (p : ℝ)).div_const (p : ℝ)
      rw [← Real.sinc_of_ne_zero hp] at h
      convert h using 1
      · ext n
        simp only [callbackBias, square_pow, coefficient, denominator, degree,
          AlternatingEnclosure.sign_eq, pow_succ, div_eq_mul_inv]
        field_simp
      · rfl

/-- Cauchy's product turns geometric averaging of partial sums into coefficient weighting. -/
theorem geometric_partial_expectation (b : ℕ → ℝ) (hb : Summable (fun n => ‖b n‖))
    (q : ℝ) (hq : 0 ≤ q) (hq' : q < 1) :
    HasSum (fun n => (1 - q) * q ^ n * ∑ j ∈ range (n + 1), b j)
      (∑' n, q ^ n * b n) := by
  have hf : Summable (fun n => ‖q ^ n * b n‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hb
    intro n
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq n)]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hq hq'.le)
  have hg := hasSum_geometric_of_lt_one hq hq'
  have hgn : Summable (fun n : ℕ => ‖q ^ n‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq _)] using hg.summable
  have hc := hasSum_sum_range_mul_of_summable_norm hf hgn
  rw [hg.tsum_eq] at hc
  have hconv (n : ℕ) :
      (∑ j ∈ range (n + 1), (q ^ j * b j) * q ^ (n - j)) =
        q ^ n * ∑ j ∈ range (n + 1), b j := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [mul_right_comm, ← pow_add, Nat.add_sub_of_le hjn]
  have h := hc.mul_left (1 - q)
  simp_rw [hconv] at h
  have he : (1 - q) * ((∑' n, q ^ n * b n) * (1 - q)⁻¹) = ∑' n, q ^ n * b n := by
    field_simp [sub_ne_zero.mpr hq'.ne']
  simpa only [he, mul_assoc] using h

end

end SampLib.FactorialSeries
