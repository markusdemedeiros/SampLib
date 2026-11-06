import SampLib.Bernoulli.Laws.Addition
import SampLib.Bernoulli.Laws.Complement

/-! # Laws of subtraction by complement and addition

Complementing a coin of bias `(1-p)+q` gives bias `p-q`. This module defines that bias and
proves that negating the output transports every continuation credit.
-/

open scoped ENNReal

namespace SampLib.Subtraction

noncomputable section

/-- The complemented first coin plus the second coin meets the addition margin. -/
theorem complement_bound (p q : unitInterval) (e f : ℤ)
    (h : (e : ℝ) / f ≤ (p : ℝ) - q) :
    (unitInterval.symm p : ℝ) + q ≤ 1 - (e : ℝ) / f := by
  rw [unitInterval.coe_symm_eq]
  linarith

/-- The difference bias, normalized by its supplied positive lower margin. -/
def bias (p q : unitInterval) (e f : ℤ) (he : 0 < e) (hef : e < f)
    (h : (e : ℝ) / f ≤ (p : ℝ) - q) : unitInterval :=
  unitInterval.symm (Addition.bias (unitInterval.symm p) q e f he hef
    (complement_bound p q e f h))

/-- The difference bias is `p - q`. -/
theorem bias_coe (p q : unitInterval) (e f : ℤ) (he : 0 < e) (hef : e < f)
    (h : (e : ℝ) / f ≤ (p : ℝ) - q) : (bias p q e f he hef h : ℝ) = (p : ℝ) - q := by
  simp only [bias, unitInterval.coe_symm_eq, Addition.bias_coe]
  ring

/-- Negation swaps the addition law's two atoms, with no restriction on the credits. -/
theorem expectation (p q : unitInterval) (e f : ℤ) (he : 0 < e) (hef : e < f)
    (h : (e : ℝ) / f ≤ (p : ℝ) - q) (F : Bool → ℝ≥0∞) :
    ∫⁻ b, F (!b) ∂RealCoin.law
      (Addition.bias (unitInterval.symm p) q e f he hef (complement_bound p q e f h)) =
      ∫⁻ b, F b ∂RealCoin.law (bias p q e f he hef h) :=
  Complement.expectation_preservation _ F

end

end SampLib.Subtraction
