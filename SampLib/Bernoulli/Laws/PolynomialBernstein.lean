module

public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Tactic

@[expose] public section

/-! # Exact conversion of power coefficients to Bernstein coefficients

The binomial factorial-moment identity expresses every monomial in a Bernstein
basis of higher degree. Linearity gives exactly the coefficient formula used by
the sampler's conversion loop, with no approximation to the target polynomial.
-/

open Finset
open scoped BigOperators unitInterval

namespace SampLib.PolynomialBernstein

noncomputable section

/-- A finite power-basis polynomial, including its constant term. -/
def value (a : ℕ → ℝ) (d : ℕ) (x : ℝ) : ℝ := ∑ j ∈ range (d + 1), a j * x ^ j

/-- The exact degree-`n` Bernstein coefficient computed by the source. -/
def coefficient (a : ℕ → ℝ) (d n k : ℕ) : ℝ :=
  ∑ j ∈ range (d + 1), a j * ((Nat.choose k j : ℝ) / (Nat.choose n j : ℝ))

theorem continuous_value (a : ℕ → ℝ) (d : ℕ) : Continuous (value a d) := by
  apply continuous_finsetSum
  intro j _
  fun_prop

private theorem moment_term (n j k : ℕ) (x : I) :
    (Nat.choose (j + k) j : ℝ) * bernstein n (j + k) x =
      (Nat.choose n j : ℝ) * (x : ℝ) ^ j * bernstein (n - j) k x := by
  have hc : (Nat.choose (j + k) j : ℝ) * Nat.choose n (j + k) =
      (Nat.choose n j : ℝ) * Nat.choose (n - j) k := by
    have h := Nat.choose_mul (n := n) (k := j + k) (s := j) (Nat.le_add_right j k)
    exact_mod_cast (by simpa [Nat.mul_comm] using h)
  rw [bernstein_apply, bernstein_apply,
    show n - (j + k) = n - j - k by omega, pow_add]
  calc
    _ = ((Nat.choose (j + k) j : ℝ) * Nat.choose n (j + k)) *
        (x : ℝ) ^ j * ((x : ℝ) ^ k * (1 - (x : ℝ)) ^ (n - j - k)) := by ring
    _ = _ := by rw [hc]; ring

/-- The factorial moment of a binomial law is a monomial. -/
theorem monomial_moment {n j : ℕ} (hj : j ≤ n) (x : I) :
    (∑ k ∈ range (n + 1), (Nat.choose k j : ℝ) * bernstein n k x) =
      (Nat.choose n j : ℝ) * (x : ℝ) ^ j := by
  rw [show n + 1 = j + (n - j + 1) by omega, sum_range_add]
  have hz : (∑ k ∈ range j, (Nat.choose k j : ℝ) * bernstein n k x) = 0 := by
    apply sum_eq_zero
    intro k hk
    simp [Nat.choose_eq_zero_of_lt (mem_range.mp hk)]
  rw [hz, zero_add]
  have hs : (∑ k ∈ range (n - j + 1), bernstein (n - j) k x) = 1 := by
    simpa only [sum_range] using bernstein.probability (n - j) x
  calc
    _ = ∑ k ∈ range (n - j + 1),
        ((Nat.choose n j : ℝ) * (x : ℝ) ^ j) * bernstein (n - j) k x := by
      apply sum_congr rfl
      intro k _
      exact moment_term n j k x
    _ = ((Nat.choose n j : ℝ) * (x : ℝ) ^ j) *
        (∑ k ∈ range (n - j + 1), bernstein (n - j) k x) := (mul_sum ..).symm
    _ = _ := by rw [hs, mul_one]

theorem monomial_representation {n j : ℕ} (hj : j ≤ n) (x : I) :
    (∑ k ∈ range (n + 1),
      ((Nat.choose k j : ℝ) / (Nat.choose n j : ℝ)) * bernstein n k x) = (x : ℝ) ^ j := by
  have hc : (Nat.choose n j : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj).ne'
  calc
    _ = (∑ k ∈ range (n + 1), (Nat.choose k j : ℝ) * bernstein n k x) /
        (Nat.choose n j : ℝ) := by
      rw [sum_div]
      apply sum_congr rfl
      intro k _
      ring
    _ = ((Nat.choose n j : ℝ) * (x : ℝ) ^ j) / (Nat.choose n j : ℝ) := by
      rw [monomial_moment hj]
    _ = _ := by field_simp

/-- Evaluating any elevated Bernstein representation recovers the exact input polynomial. -/
theorem evaluation (a : ℕ → ℝ) (d n : ℕ) (hn : d ≤ n) (x : I) :
    (∑ k ∈ range (n + 1), coefficient a d n k * bernstein n k x) = value a d x := by
  unfold coefficient value
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  have hjn : j ≤ n := (Nat.le_of_lt_succ (mem_range.mp hj)).trans hn
  calc
    _ = a j * (∑ k ∈ range (n + 1),
        ((Nat.choose k j : ℝ) / (Nat.choose n j : ℝ)) * bernstein n k x) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [monomial_representation hjn]

end

end SampLib.PolynomialBernstein
