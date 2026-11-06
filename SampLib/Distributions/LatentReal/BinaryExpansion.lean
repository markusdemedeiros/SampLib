module

public import SampLib.Distributions.LatentReal.DigitPosterior
public import SampLib.Distributions.DyadicPosterior
public import Mathlib.Analysis.Real.OfDigits

/-! # Real values represented by dependent binary digits

Closed dyadic enclosures work for every stream, including eventually constant
streams and the all-ones representation of one. No null-boundary assumption is
needed until a caller attempts a discontinuous observation such as floor.
-/

@[expose] public section

open Set MeasureTheory

namespace SampLib.DigitPosterior

noncomputable section

/-- Interpret a Boolean as a binary digit. -/
def binary (b : Bool) : Fin 2 := if b then 1 else 0

/-- The real represented by a stream; both binary representations are permitted. -/
def value (digits : ℕ → Bool) : ℝ := Real.ofDigits (fun n => binary (digits n))

theorem value_nonneg (digits : ℕ → Bool) : 0 ≤ value digits := Real.ofDigits_nonneg _

theorem value_le_one (digits : ℕ → Bool) : value digits ≤ 1 := Real.ofDigits_le_one _

@[simp] theorem value_false : value (fun _ => false) = 0 := by
  simp [value, Real.ofDigits, Real.ofDigitsTerm, binary]

@[simp] theorem value_true : value (fun _ => true) = 1 := by
  simpa [value, binary] using Real.ofDigits_const_last_eq_one' (b := 2) (by decide)

theorem measurable_value {Ω : Type} [MeasurableSpace Ω] {digits : Ω → ℕ → Bool}
    (hd : ∀ n, Measurable (fun x => digits x n)) : Measurable (fun x => value (digits x)) := by
  apply Real.continuous_ofDigits.measurable.comp
  exact Measurable.of_eval fun n => (measurable_of_finite binary).comp (hd n)

/-- The head digit has weight one half; the remaining stream occupies the other half. -/
theorem value_shift (digits : ℕ → Bool) :
    value digits = DyadicPosterior.half (digits 0) (value (fun n => digits (n + 1))) := by
  rw [value, Real.ofDigits_eq_sum_add_ofDigits _ 1]
  simp only [Finset.sum_range_one, Real.ofDigitsTerm, zero_add, pow_one]
  cases h : digits 0 <;> simp [binary, value, DyadicPosterior.half] <;> ring

end

end SampLib.DigitPosterior
