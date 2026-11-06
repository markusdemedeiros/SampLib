module

public import SampLib.Distributions.EnvelopeShadow
public import SampLib.Distributions.ReverseBinomial
public import Mathlib.Analysis.SpecialFunctions.Bernstein

@[expose] public section

/-! # Rational contracts for the actual Bernstein-envelope callbacks

Only visited degrees and valid head counts are constrained. Consistency is
reverse-hypergeometric degree elevation; convergence concerns the Bernstein
means, not pointwise enclosure by each random shadow interval.
-/

open Finset Filter
open scoped Topology

namespace SampLib.EnvelopeFactory

noncomputable section

structure Coefficients where
  degree : ℕ → ℕ
  initial_degree : degree 0 = 0
  grows : ∀ t, degree t < degree (t + 1)
  lower : (t : ℕ) → Fin (degree t + 1) → ℚ
  upper : (t : ℕ) → Fin (degree t + 1) → ℚ
  bounds : ∀ t k, 0 ≤ lower t k ∧ lower t k ≤ upper t k ∧ upper t k ≤ 1
  lower_initial : ∀ k, lower 0 k = 0
  upper_initial : ∀ k, upper 0 k = 1
  lower_consistent : ∀ t (k : Fin (degree (t + 1) + 1)),
    (∑ j : Fin (degree t + 1),
      ReverseBinomial.coefficient (degree t) (degree (t + 1)) k j * lower t j) ≤
        lower (t + 1) k
  upper_consistent : ∀ t (k : Fin (degree (t + 1) + 1)), upper (t + 1) k ≤
    ∑ j : Fin (degree t + 1),
      ReverseBinomial.coefficient (degree t) (degree (t + 1)) k j * upper t j

namespace Coefficients

variable (a : Coefficients)

@[reducible] def toScheme : Scheme where
  degree := a.degree
  initial_degree := a.initial_degree
  grows := a.grows
  lower t k := (a.lower t k : ℝ)
  upper t k := (a.upper t k : ℝ)
  bounds t k := ⟨by exact_mod_cast (a.bounds t k).1,
    by exact_mod_cast (a.bounds t k).2.1, by exact_mod_cast (a.bounds t k).2.2⟩
  lower_initial k := by simp only [a.lower_initial, Rat.cast_zero]
  upper_initial k := by simp only [a.upper_initial, Rat.cast_one]
  reverse t k j := (ReverseBinomial.coefficient (a.degree t) (a.degree (t + 1)) k j : ℝ)
  reverse_nonneg t k j := by exact_mod_cast
    ReverseBinomial.coefficient_nonneg (a.degree t) (a.degree (t + 1)) k j
  reverse_sum t k := by
    rw [Fin.sum_univ_eq_sum_range (fun j =>
      (ReverseBinomial.coefficient (a.degree t) (a.degree (t + 1)) k j : ℝ))]
    exact ReverseBinomial.coefficient_sum_degree_real (a.degree t) (a.degree (t + 1)) k
      (a.grows t).le (Nat.le_of_lt_succ k.isLt)
  lower_consistent t k := by
    change (∑ j : Fin (a.degree t + 1),
      (ReverseBinomial.coefficient (a.degree t) (a.degree (t + 1)) k j : ℝ) *
        (a.lower t j : ℝ)) ≤ (a.lower (t + 1) k : ℝ)
    exact_mod_cast a.lower_consistent t k
  upper_consistent t k := by
    change (a.upper (t + 1) k : ℝ) ≤ ∑ j : Fin (a.degree t + 1),
      (ReverseBinomial.coefficient (a.degree t) (a.degree (t + 1)) k j : ℝ) *
        (a.upper t j : ℝ)
    exact_mod_cast a.upper_consistent t k

/-- The Bernstein mean of a rational row. -/
def rowMean (t : ℕ) (row : Fin (a.degree t + 1) → ℚ) (p : unitInterval) : ℝ :=
  ∑ k : Fin (a.degree t + 1), bernstein (a.degree t) k p * (row k : ℝ)

def lowerMean (t : ℕ) (p : unitInterval) : ℝ := a.rowMean t (a.lower t) p
def upperMean (t : ℕ) (p : unitInterval) : ℝ := a.rowMean t (a.upper t) p

end Coefficients

/-- A coefficient contract whose Bernstein means share a limit at the input bias `p`. -/
structure Parameters (p : unitInterval) extends Coefficients where
  target : unitInterval
  lower_converges : Tendsto (fun t => toCoefficients.lowerMean t p) atTop (𝓝 (target : ℝ))
  upper_converges : Tendsto (fun t => toCoefficients.upperMean t p) atTop (𝓝 (target : ℝ))

theorem Parameters.width_vanishes {p : unitInterval} (a : Parameters p) :
    Tendsto (fun t => a.toCoefficients.upperMean t p - a.toCoefficients.lowerMean t p)
      atTop (𝓝 (0 : ℝ)) := by
  simpa only [sub_self] using a.upper_converges.sub a.lower_converges

end

end SampLib.EnvelopeFactory
