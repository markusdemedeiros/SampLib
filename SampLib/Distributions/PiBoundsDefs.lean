import SampLib.Distributions.RealEnclosure

/-! # Exact integer states of the reciprocal-arctangent and Machin gateways -/

namespace SampLib.PiBounds

export RealEnclosure (encodeTriple)

def sign (k : ℕ) : ℤ := if k % 2 = 0 then 1 else -1

def termDenominator (q k : ℕ) : ℤ := ((2 * k + 1 : ℕ) : ℤ) * (q : ℤ) ^ (2 * k + 1)

def denominator (q : ℕ) : ℕ → ℤ
  | 0 => 1
  | k + 1 => denominator q k * termDenominator q k

def numerator (q : ℕ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => numerator q k * termDenominator q k + sign k * denominator q k

@[simp] theorem denominator_zero (q : ℕ) : denominator q 0 = 1 := rfl

@[simp] theorem denominator_succ (q k : ℕ) :
    denominator q (k + 1) = denominator q k * termDenominator q k := rfl

@[simp] theorem numerator_zero (q : ℕ) : numerator q 0 = 0 := rfl

@[simp] theorem numerator_succ (q k : ℕ) :
    numerator q (k + 1) = numerator q k * termDenominator q k + sign k * denominator q k := rfl

theorem power_succ (q k : ℕ) :
    (q : ℤ) ^ (2 * (k + 1) + 1) = (q : ℤ) ^ (2 * k + 1) * q * q := by
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, pow_add]
  ring

/-- Neighboring alternating partial sums, at the source's unreduced denominator. -/
def arctanRaw (q n : ℕ) : ℤ × (ℤ × ℤ) :=
  let middle := numerator q n * termDenominator q n
  let d := denominator q n
  (if n % 2 = 0 then middle else middle - d,
    (if n % 2 = 0 then middle + d else middle, d * termDenominator q n))

/-- Machin's linear combination, with cross-multiplied integer endpoints. -/
def piRaw (n : ℕ) : ℤ × (ℤ × ℤ) :=
  let a := arctanRaw 5 (n + 1)
  let b := arctanRaw 239 (n + 1)
  (16 * a.1 * b.2.2 - 4 * b.2.1 * a.2.2,
    (16 * a.2.1 * b.2.2 - 4 * b.1 * a.2.2, a.2.2 * b.2.2))

theorem termDenominator_pos (q k : ℕ) (hq : 2 ≤ q) : 0 < termDenominator q k := by
  have hq0 : (0 : ℤ) < q := by omega
  unfold termDenominator
  exact mul_pos (by omega) (pow_pos hq0 _)

theorem denominator_pos (q k : ℕ) (hq : 2 ≤ q) : 0 < denominator q k := by
  induction k with
  | zero => simp
  | succ k IH => exact mul_pos IH (termDenominator_pos q k hq)

theorem arctanRaw_den_pos (q n : ℕ) (hq : 2 ≤ q) : 0 < (arctanRaw q n).2.2 :=
  mul_pos (denominator_pos q n hq) (termDenominator_pos q n hq)

theorem piRaw_den_pos (n : ℕ) : 0 < (piRaw n).2.2 :=
  mul_pos (arctanRaw_den_pos 5 (n + 1) (by decide))
    (arctanRaw_den_pos 239 (n + 1) (by decide))

end SampLib.PiBounds
