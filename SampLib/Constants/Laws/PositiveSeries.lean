import SampLib.Common.Laws.BoundsKernel

/-! # Canonical positive rational series and their enclosures

The accumulator represents the finite prefix sum exactly. Its next term and
certified remainder enclose the ordinary convergent series, with width equal to
the supplied remainder bound. This gives the finite-horizon credit profile used
by the program proof.
-/

open Finset

namespace SampLib.FromPositiveSeries

noncomputable section

/-- One nonnegative rational term and a nonnegative rational bound on the remaining sum. -/
structure Coefficient where
  numerator : ℕ
  denominator : ℕ
  positive : 0 < denominator
  errorNumerator : ℕ
  errorDenominator : ℕ
  errorPositive : 0 < errorDenominator

def Coefficient.value (c : Coefficient) : ℝ := c.numerator / (c.denominator : ℝ)

def Coefficient.error (c : Coefficient) : ℝ := c.errorNumerator / (c.errorDenominator : ℝ)

theorem Coefficient.value_nonneg (c : Coefficient) : 0 ≤ c.value := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- A convergent series of probability mass at most one, with arbitrarily tight tail bounds. -/
structure Parameters where
  coefficient : ℕ → Coefficient
  summable : Summable (fun n => (coefficient n).value)
  mass_le_one : (∑' n, (coefficient n).value) ≤ 1
  remainder : ∀ n, (∑' i, (coefficient i).value) ≤
    (∑ i ∈ range (n + 1), (coefficient i).value) + (coefficient n).error
  tight : ∀ ε : ℝ, 0 < ε → ∃ n, (coefficient n).error ≤ ε

/-- The target is the ordinary sum of the supplied positive rational terms. -/
def bias (a : Parameters) : unitInterval :=
  ⟨∑' n, (a.coefficient n).value,
    tsum_nonneg (fun n => (a.coefficient n).value_nonneg), a.mass_le_one⟩

/-- The unreduced fraction maintained by the actual accumulator. -/
structure Fraction where
  numerator : ℕ
  denominator : ℕ
  positive : 0 < denominator

def Fraction.value (x : Fraction) : ℝ := x.numerator / (x.denominator : ℝ)

def Fraction.add (x : Fraction) (c : Coefficient) : Fraction :=
  ⟨x.numerator * c.denominator + c.numerator * x.denominator,
    x.denominator * c.denominator, Nat.mul_pos x.positive c.positive⟩

/-- The callback at `n` is added before its remainder is tested. -/
def accumulator (a : Parameters) : ℕ → Fraction
  | 0 => ⟨0, 1, by decide⟩
  | n + 1 => (accumulator a n).add (a.coefficient n)

theorem Fraction.value_add (x : Fraction) (c : Coefficient) :
    (x.add c).value = x.value + c.value := by
  have hx : (0 : ℝ) < x.denominator := by exact_mod_cast x.positive
  have hc : (0 : ℝ) < c.denominator := by exact_mod_cast c.positive
  dsimp [Fraction.value, Fraction.add, Coefficient.value]
  push_cast
  field_simp

theorem value_accumulator (a : Parameters) (n : ℕ) :
    (accumulator a n).value = ∑ i ∈ range n, (a.coefficient i).value := by
  induction n with
  | zero => simp [accumulator, Fraction.value]
  | succ n IH => rw [accumulator, Fraction.value_add, IH, sum_range_succ]

theorem accumulator_le_bias (a : Parameters) (n : ℕ) :
    (accumulator a n).value ≤ (bias a : ℝ) := by
  rw [value_accumulator]
  exact a.summable.sum_le_tsum (range n) (fun i _ => (a.coefficient i).value_nonneg)

private theorem upper_ratio (x : Fraction) (c : Coefficient) :
    ((x.numerator * c.errorDenominator + c.errorNumerator * x.denominator : ℕ) : ℝ) /
        ((x.denominator * c.errorDenominator : ℕ) : ℝ) = x.value + c.error := by
  have hx : (0 : ℝ) < x.denominator := by exact_mod_cast x.positive
  have hc : (0 : ℝ) < c.errorDenominator := by exact_mod_cast c.errorPositive
  dsimp [Fraction.value, Coefficient.error]
  push_cast
  field_simp

private theorem lower_ratio (x : Fraction) (c : Coefficient) :
    ((x.numerator * c.errorDenominator : ℕ) : ℝ) /
        ((x.denominator * c.errorDenominator : ℕ) : ℝ) = x.value := by
  have hx : (0 : ℝ) < x.denominator := by exact_mod_cast x.positive
  have hc : (0 : ℝ) < c.errorDenominator := by exact_mod_cast c.errorPositive
  dsimp [Fraction.value]
  push_cast
  field_simp

/-- A common-denominator enclosure of the canonical sum after term `n`. -/
def enclosure (a : Parameters) (n : ℕ) : FromBounds.Interval (bias a) where
  lower := ((accumulator a (n + 1)).numerator * (a.coefficient n).errorDenominator : ℕ)
  upper := ((accumulator a (n + 1)).numerator * (a.coefficient n).errorDenominator +
    (a.coefficient n).errorNumerator * (accumulator a (n + 1)).denominator : ℕ)
  denominator := (accumulator a (n + 1)).denominator * (a.coefficient n).errorDenominator
  positive := Nat.mul_pos (accumulator a (n + 1)).positive (a.coefficient n).errorPositive
  below := by
    have hd : (0 : ℝ) <
        ((accumulator a (n + 1)).denominator * (a.coefficient n).errorDenominator : ℕ) := by
      exact_mod_cast Nat.mul_pos (accumulator a (n + 1)).positive (a.coefficient n).errorPositive
    simp only [Int.cast_natCast]
    apply (div_le_iff₀ hd).mp
    rw [lower_ratio]
    exact accumulator_le_bias a (n + 1)
  above := by
    have hd : (0 : ℝ) <
        ((accumulator a (n + 1)).denominator * (a.coefficient n).errorDenominator : ℕ) := by
      exact_mod_cast Nat.mul_pos (accumulator a (n + 1)).positive (a.coefficient n).errorPositive
    simp only [Int.cast_natCast]
    apply (le_div_iff₀ hd).mp
    rw [upper_ratio, value_accumulator]
    exact a.remainder n

theorem enclosure_left (a : Parameters) (n : ℕ) :
    (enclosure a n).left = (accumulator a (n + 1)).value := by
  simpa only [FromBounds.Interval.left, enclosure, Int.cast_natCast] using
    lower_ratio (accumulator a (n + 1)) (a.coefficient n)

theorem enclosure_right (a : Parameters) (n : ℕ) :
    (enclosure a n).right = (accumulator a (n + 1)).value + (a.coefficient n).error := by
  simpa only [FromBounds.Interval.right, enclosure, Int.cast_natCast] using
    upper_ratio (accumulator a (n + 1)) (a.coefficient n)

theorem enclosure_width (a : Parameters) (n : ℕ) :
    (enclosure a n).width = (a.coefficient n).error := by
  rw [FromBounds.Interval.width, enclosure_left, enclosure_right]
  ring

theorem enclosures_tight (a : Parameters) : FromBounds.Tight (enclosure a) := by
  intro ε hε
  obtain ⟨n, hn⟩ := a.tight ε hε
  exact ⟨n, by simpa only [enclosure_width] using hn⟩

/-- The program's numerator update is the next accumulator numerator. -/
theorem numerator_step (a : Parameters) (n : ℕ) :
    ((accumulator a n).numerator : ℤ) * (a.coefficient n).denominator +
        (a.coefficient n).numerator * ((accumulator a n).denominator : ℤ) =
      ((accumulator a (n + 1)).numerator : ℤ) := by
  simp [accumulator, Fraction.add, Nat.cast_add, Nat.cast_mul]

/-- The program's denominator update is the next accumulator denominator. -/
theorem denominator_step (a : Parameters) (n : ℕ) :
    ((accumulator a n).denominator : ℤ) * (a.coefficient n).denominator =
      ((accumulator a (n + 1)).denominator : ℤ) := by
  simp [accumulator, Fraction.add, Nat.cast_mul]

/-- The program's upper numerator is the enclosure's upper endpoint. -/
theorem upper_numerator_step (a : Parameters) (n : ℕ) :
    ((accumulator a (n + 1)).numerator : ℤ) * (a.coefficient n).errorDenominator +
        (a.coefficient n).errorNumerator * ((accumulator a (n + 1)).denominator : ℤ) =
      (enclosure a n).upper := by
  simp [enclosure, Nat.cast_add, Nat.cast_mul]

/-- The program's upper denominator is the enclosure's denominator. -/
theorem upper_denominator_step (a : Parameters) (n : ℕ) :
    ((accumulator a (n + 1)).denominator : ℤ) * (a.coefficient n).errorDenominator =
      ((enclosure a n).denominator : ℤ) := by
  simp [enclosure, Nat.cast_mul]

theorem lower_denominator_pos (a : Parameters) (n : ℕ) :
    (0 : ℤ) < (accumulator a (n + 1)).denominator := by
  exact_mod_cast (accumulator a (n + 1)).positive

theorem upper_denominator_pos (a : Parameters) (n : ℕ) :
    (0 : ℤ) < (enclosure a n).denominator := by exact_mod_cast (enclosure a n).positive

/-- Resolving the accumulator fraction resolves the left endpoint. -/
theorem lower_resolves (a : Parameters) (n : ℕ) {q : List Bool} {b : Bool}
    (h : DyadicPosterior.resolves q
      ((((accumulator a (n + 1)).numerator : ℤ) : ℝ) /
        (((accumulator a (n + 1)).denominator : ℤ) : ℝ)) b) :
    DyadicPosterior.resolves q (enclosure a n).left b := by
  simpa only [enclosure_left, Fraction.value, Int.cast_natCast] using h

/-- Resolving the upper fraction resolves the right endpoint. -/
theorem upper_resolves (a : Parameters) (n : ℕ) {q : List Bool} {b : Bool}
    (h : DyadicPosterior.resolves q
      (((enclosure a n).upper : ℝ) / (((enclosure a n).denominator : ℤ) : ℝ)) b) :
    DyadicPosterior.resolves q (enclosure a n).right b := by
  simpa only [FromBounds.Interval.right, Int.cast_natCast] using h

end

end SampLib.FromPositiveSeries
