import SampLib.FactoryFractions
import SampLib.Distributions.PolynomialBernsteinElevation

/-! Exact rational data for the power-basis polynomial factory. -/

open Set
open Finset (range)
open scoped unitInterval

namespace SampLib.PolynomialFactory

open FactoryFractions

/-- A default only used beyond the input list. -/
def zeroFraction : Fraction := ⟨0, 1, by decide⟩

def input (xs : List Fraction) (j : ℕ) : Fraction := xs[j]?.getD zeroFraction

def degree (xs : List Fraction) : ℕ := xs.length - 1

/-- Exact elevated coefficients, before the source's admissibility check. -/
def coefficient (xs : List Fraction) (n k : ℕ) : ℚ :=
  ∑ j ∈ range xs.length, (input xs j).value * ((Nat.choose k j : ℚ) / Nat.choose n j)

/-- The real input polynomial. -/
def value (xs : List Fraction) (x : ℝ) : ℝ :=
  PolynomialBernstein.value (fun j => ((input xs j).value : ℝ)) (degree xs) x

/-- A degree accepted by the source's exact rational checks. -/
def Admissible (xs : List Fraction) (n : ℕ) : Prop :=
  degree xs ≤ n ∧ ∀ k ≤ n, coefficient xs n k ∈ Icc 0 1

theorem cast_coefficient (xs : List Fraction) (hxs : xs ≠ []) (n k : ℕ) :
    (coefficient xs n k : ℝ) =
      PolynomialBernstein.coefficient (fun j => ((input xs j).value : ℝ)) (degree xs) n k := by
  have hlen : degree xs + 1 = xs.length := by
    have := List.length_pos_iff.mpr hxs
    simp only [degree]
    omega
  simp only [coefficient, PolynomialBernstein.coefficient, hlen, Rat.cast_sum,
    Rat.cast_mul, Rat.cast_div, Rat.cast_natCast]

/-- Strict probability polynomials always reach an admissible degree. -/
theorem exists_admissible (xs : List Fraction) (hxs : xs ≠ [])
    (h : ∀ x : unitInterval, value xs x ∈ Ioo 0 1) : ∃ n, Admissible xs n := by
  obtain ⟨n, hn, hc⟩ := PolynomialBernstein.exists_admissible_degree
    (fun j => ((input xs j).value : ℝ)) (degree xs) h
  refine ⟨n, hn, fun k hk => ?_⟩
  have hc' := hc k hk
  rw [← cast_coefficient xs hxs n k] at hc'
  exact ⟨by exact_mod_cast hc'.1, by exact_mod_cast hc'.2⟩

/-- An admissible representation certifies the polynomial's probability range. -/
theorem value_mem (xs : List Fraction) (hxs : xs ≠ []) (n : ℕ)
    (h : Admissible xs n) (p : unitInterval) : value xs p ∈ Icc 0 1 := by
  have he := PolynomialBernstein.evaluation
    (fun j => ((input xs j).value : ℝ)) (degree xs) n h.1 p
  simp_rw [← cast_coefficient xs hxs] at he
  have hc (k : ℕ) (hk : k ∈ range (n + 1)) :
      (coefficient xs n k : ℝ) ∈ Icc 0 1 := by
    have hk' := h.2 k (by have := Finset.mem_range.mp hk; omega)
    exact ⟨by exact_mod_cast hk'.1, by exact_mod_cast hk'.2⟩
  have hs : (∑ k ∈ range (n + 1), bernstein n k p) = 1 := by
    simpa only [Finset.sum_range] using bernstein.probability n p
  unfold value
  rw [← he]
  constructor
  · exact Finset.sum_nonneg fun k hk => mul_nonneg (hc k hk).1 bernstein_nonneg
  · calc
      _ ≤ ∑ k ∈ range (n + 1), bernstein n k p := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_of_le_one_left bernstein_nonneg (hc k hk).2
      _ = 1 := hs

noncomputable def bias (xs : List Fraction) (hxs : xs ≠ [])
    (h : ∃ n, Admissible xs n) (p : unitInterval) : unitInterval :=
  ⟨value xs p, value_mem xs hxs h.choose h.choose_spec p⟩

@[simp] theorem bias_coe (xs : List Fraction) (hxs : xs ≠ [])
    (h : ∃ n, Admissible xs n) (p : unitInterval) : (bias xs hxs h p : ℝ) = value xs p := rfl

end SampLib.PolynomialFactory
