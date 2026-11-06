module

public import SampLib.Distributions.EnvelopeCoefficients

@[expose] public section

/-! # Exact rational thresholds for the envelope program

The rational accumulator follows the shadow-history recurrence exactly. Its real
image supplies the probabilistic invariant; no rounding or interval oracle is used.
-/

open Finset

namespace SampLib.EnvelopeFactory.Coefficients

noncomputable section

variable (a : Coefficients)

def lowerBarQ (t : ℕ) (k : Fin (a.degree (t + 1) + 1)) : ℚ :=
  ∑ j : Fin (a.degree t + 1),
    ReverseBinomial.coefficient (a.degree t) (a.degree (t + 1)) k j * a.lower t j

def upperBarQ (t : ℕ) (k : Fin (a.degree (t + 1) + 1)) : ℚ :=
  ∑ j : Fin (a.degree t + 1),
    ReverseBinomial.coefficient (a.degree t) (a.degree (t + 1)) k j * a.upper t j

@[simp] theorem lowerBarQ_coe (t : ℕ) (k : Fin (a.degree (t + 1) + 1)) :
    (a.lowerBarQ t k : ℝ) = a.toScheme.lowerBar t k := by
  simp [lowerBarQ, Scheme.lowerBar, mean, toScheme]

@[simp] theorem upperBarQ_coe (t : ℕ) (k : Fin (a.degree (t + 1) + 1)) :
    (a.upperBarQ t k : ℝ) = a.toScheme.upperBar t k := by
  simp [upperBarQ, Scheme.upperBar, mean, toScheme]

def thresholdsQ (a : Coefficients) :
    (t : ℕ) → Fin (a.degree t + 1) → a.toScheme.Past t → ℚ × ℚ
  | 0, _, _ => (0, 1)
  | t + 1, k, (h, j) =>
      let previous := thresholdsQ a t j h
      let factor := (previous.2 - previous.1) / (a.upperBarQ t k - a.lowerBarQ t k)
      (previous.1 + (a.lower (t + 1) k - a.lowerBarQ t k) * factor,
       previous.2 - (a.upperBarQ t k - a.upper (t + 1) k) * factor)

theorem thresholdsQ_coe (t : ℕ) (k : Fin (a.degree t + 1)) (h : a.toScheme.Past t) :
    ((a.thresholdsQ t k h).1 : ℝ) = (a.toScheme.thresholds t k h).1 ∧
      ((a.thresholdsQ t k h).2 : ℝ) = (a.toScheme.thresholds t k h).2 := by
  induction t with
  | zero => exact ⟨Rat.cast_zero, Rat.cast_one⟩
  | succ t IH =>
    rcases h with ⟨h, j⟩
    simp only [thresholdsQ, Scheme.thresholds, Rat.cast_add, Rat.cast_sub, Rat.cast_mul,
      Rat.cast_div, a.lowerBarQ_coe, a.upperBarQ_coe, (IH j h).1, (IH j h).2,
      lowerUpdate, upperUpdate, toScheme]
    constructor <;> ring

/-- The denominator is positive on every reachable unresolved history. -/
theorem oldWidthQ_pos (t : ℕ) (k : Fin (a.degree (t + 1) + 1))
    (h : a.toScheme.Past t) (j : Fin (a.degree t + 1))
    (hh : 0 < a.toScheme.weight t j h)
    (hj : 0 < a.toScheme.reverse t k j)
    (hwidth : (a.thresholdsQ t j h).1 < (a.thresholdsQ t j h).2) :
    0 < a.upperBarQ t k - a.lowerBarQ t k := by
  have hw : (a.toScheme.thresholds t j h).1 < (a.toScheme.thresholds t j h).2 := by
    rw [← (a.thresholdsQ_coe t j h).1, ← (a.thresholdsQ_coe t j h).2]
    exact_mod_cast hwidth
  have hp := a.toScheme.old_width_pos t k h j hh hj hw
  have hp' : (0 : ℝ) < (a.upperBarQ t k : ℝ) - (a.lowerBarQ t k : ℝ) := by
    simpa only [a.upperBarQ_coe, a.lowerBarQ_coe] using hp
  exact_mod_cast hp'

end

end SampLib.EnvelopeFactory.Coefficients
