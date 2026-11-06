module

public import SampLib.Distributions.FactorialSeries

@[expose] public section

/-! # Exact integer states of factorial-series refinement -/

namespace SampLib.FactorialSeries

noncomputable section

def numerator (m : Mode) : ℕ → ℤ
  | 0 => 1
  | n + 1 => numerator m n * factor m n + if (n + 1) % 2 = 0 then 1 else -1

private theorem cast_sign (n : ℕ) :
    ((if n % 2 = 0 then 1 else -1 : ℤ) : ℝ) = AlternatingEnclosure.sign n := by
  by_cases hn : n % 2 = 0 <;> simp [AlternatingEnclosure.sign, hn]

/-- The scaled partial sums have integer numerators at their factorial denominators. -/
theorem numerator_real (m : Mode) (n : ℕ) :
    (numerator m n : ℝ) = partialSum m n * denominator m n := by
  induction n with
  | zero => simp [numerator, partialSum]
  | succ n IH =>
    have hd : (denominator m (n + 1) : ℝ) ≠ 0 := by
      exact_mod_cast (denominator_pos m (n + 1)).ne'
    have hstep : partialSum m (n + 1) = partialSum m n +
        AlternatingEnclosure.sign (n + 1) * (denominator m (n + 1) : ℝ)⁻¹ :=
      AlternatingEnclosure.partial_succ (coefficient m) n
    rw [numerator, Int.cast_add, Int.cast_mul, Int.cast_natCast, cast_sign, IH,
      hstep, add_mul, mul_assoc (AlternatingEnclosure.sign (n + 1)),
      inv_mul_cancel₀ hd, mul_one,
      denominator_succ, Nat.cast_mul]
    ring

/-- State denominators are already scaled for the next coefficient. -/
def stateDenominator (m : Mode) (n : ℕ) : ℕ := denominator m (n + 1)

def lowerNumerator (m : Mode) (n : ℕ) : ℤ :=
  (numerator m n - if n % 2 = 0 then 1 else 0) * factor m n

def upperNumerator (m : Mode) (n : ℕ) : ℤ :=
  (numerator m n + if n % 2 = 0 then 0 else 1) * factor m n

@[simp] theorem lowerNumerator_zero (m : Mode) : lowerNumerator m 0 = 0 := by
  simp [lowerNumerator, numerator]

@[simp] theorem upperNumerator_zero (m : Mode) :
    upperNumerator m 0 = stateDenominator m 0 := by
  simp [upperNumerator, numerator, stateDenominator, denominator_succ]

theorem lower_ratio (m : Mode) (n : ℕ) :
    (lowerNumerator m n : ℝ) / stateDenominator m n = lower m n := by
  have hd : (denominator m n : ℝ) ≠ 0 := by exact_mod_cast (denominator_pos m n).ne'
  have hf : (factor m n : ℝ) ≠ 0 := by exact_mod_cast (factor_pos m n).ne'
  unfold lowerNumerator stateDenominator lower AlternatingEnclosure.lower
  rw [denominator_succ]
  push_cast
  rw [numerator_real]
  simp only [partialSum, coefficient]
  split_ifs <;> field_simp [hd, hf]
  all_goals ring

theorem upper_ratio (m : Mode) (n : ℕ) :
    (upperNumerator m n : ℝ) / stateDenominator m n = upper m n := by
  have hd : (denominator m n : ℝ) ≠ 0 := by exact_mod_cast (denominator_pos m n).ne'
  have hf : (factor m n : ℝ) ≠ 0 := by exact_mod_cast (factor_pos m n).ne'
  unfold upperNumerator stateDenominator upper AlternatingEnclosure.upper
  rw [denominator_succ]
  push_cast
  rw [numerator_real]
  simp only [partialSum, coefficient]
  split_ifs <;> field_simp [hd, hf]
  all_goals ring

/-- A failed callback freezes the previous partial sum. -/
def failedNumerator (m : Mode) (n : ℕ) : ℤ := numerator m n * factor m n

theorem failed_ratio (m : Mode) (n : ℕ) :
    (failedNumerator m n : ℝ) / stateDenominator m n = partialSum m n := by
  have hd : (denominator m n : ℝ) ≠ 0 := by exact_mod_cast (denominator_pos m n).ne'
  have hf : (factor m n : ℝ) ≠ 0 := by exact_mod_cast (factor_pos m n).ne'
  simp only [failedNumerator, stateDenominator, denominator_succ, Int.cast_mul,
    Int.cast_natCast, Nat.cast_mul, numerator_real]
  field_simp

/-- Raw bounds immediately after the current callback group. -/
def nextLower (m : Mode) (n : ℕ) (success : Bool) : ℤ :=
  if (n + 1) % 2 = 1 then upperNumerator m n - (if success then 1 else 0)
  else lowerNumerator m n

def nextUpper (m : Mode) (n : ℕ) (success : Bool) : ℤ :=
  if (n + 1) % 2 = 0 then lowerNumerator m n + (if success then 1 else 0)
  else upperNumerator m n

@[simp] theorem nextLower_false (m : Mode) (n : ℕ) :
    nextLower m n false = failedNumerator m n := by
  obtain hn | hn := Nat.mod_two_eq_zero_or_one n
  · have hn' : (n + 1) % 2 = 1 := by omega
    simp [nextLower, upperNumerator, failedNumerator, hn, hn']
  · have hn' : (n + 1) % 2 = 0 := by omega
    simp [nextLower, lowerNumerator, failedNumerator, hn, hn']

@[simp] theorem nextUpper_false (m : Mode) (n : ℕ) :
    nextUpper m n false = failedNumerator m n := by
  obtain hn | hn := Nat.mod_two_eq_zero_or_one n
  · have hn' : (n + 1) % 2 = 1 := by omega
    simp [nextUpper, upperNumerator, failedNumerator, hn, hn']
  · have hn' : (n + 1) % 2 = 0 := by omega
    simp [nextUpper, lowerNumerator, failedNumerator, hn, hn']

theorem nextLower_true (m : Mode) (n : ℕ) :
    nextLower m n true * factor m (n + 1) = lowerNumerator m (n + 1) := by
  obtain hn | hn := Nat.mod_two_eq_zero_or_one n
  · have hn' : (n + 1) % 2 = 1 := by omega
    simp [nextLower, upperNumerator, lowerNumerator, numerator, hn, hn', sub_eq_add_neg]
  · have hn' : (n + 1) % 2 = 0 := by omega
    simp [nextLower, lowerNumerator, numerator, hn, hn']

theorem nextUpper_true (m : Mode) (n : ℕ) :
    nextUpper m n true * factor m (n + 1) = upperNumerator m (n + 1) := by
  obtain hn | hn := Nat.mod_two_eq_zero_or_one n
  · have hn' : (n + 1) % 2 = 1 := by omega
    simp [nextUpper, upperNumerator, numerator, hn, hn']
  · have hn' : (n + 1) % 2 = 0 := by omega
    simp [nextUpper, upperNumerator, lowerNumerator, numerator, hn, hn']

/-- The successful bounds are the next enclosure before rescaling. -/
theorem nextLower_ratio (m : Mode) (n : ℕ) :
    (nextLower m n true : ℝ) / stateDenominator m n = lower m (n + 1) := by
  rw [← lower_ratio m (n + 1), ← nextLower_true]
  simp only [stateDenominator, denominator_succ, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  have hf : (factor m (n + 1) : ℝ) ≠ 0 := by exact_mod_cast (factor_pos m (n + 1)).ne'
  rw [mul_div_mul_right _ _ hf]

theorem nextUpper_ratio (m : Mode) (n : ℕ) :
    (nextUpper m n true : ℝ) / stateDenominator m n = upper m (n + 1) := by
  rw [← upper_ratio m (n + 1), ← nextUpper_true]
  simp only [stateDenominator, denominator_succ, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  have hf : (factor m (n + 1) : ℝ) ≠ 0 := by exact_mod_cast (factor_pos m (n + 1)).ne'
  rw [mul_div_mul_right _ _ hf]

end

end SampLib.FactorialSeries
