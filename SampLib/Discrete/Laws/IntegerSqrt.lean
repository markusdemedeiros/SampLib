module

public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-! # Integer Newton iteration preserves the floor square root -/

namespace SampLib.IntegerSqrt

/-- Integer Newton averaging never falls below the floor square root. -/
theorem newton_lower_bound (n x : ℕ) (hx : 0 < x) :
    Nat.sqrt n ≤ (x + n / x) / 2 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  by_contra h
  have hsum : x + n / x + 1 ≤ 2 * Nat.sqrt n := by omega
  have hdiv : n < x * (n / x + 1) := by
    have hmod := Nat.mod_lt n hx
    have hdecomp := Nat.mod_add_div n x
    nlinarith
  have hroot := Nat.sqrt_le n
  generalize hq : n / x = q at hsum hdiv
  zify at hsum hdiv hroot
  have hnonneg : 0 ≤ (2 : ℤ) * Nat.sqrt n - (x + (q : ℤ) + 1) := by omega
  have hprod := mul_nonneg hnonneg
    (show 0 ≤ (2 : ℤ) * Nat.sqrt n + (x + (q : ℤ) + 1) by positivity)
  nlinarith [sq_nonneg ((x : ℤ) - ((q : ℤ) + 1))]

/-- A nondecreasing Newton update is already at or below the floor square root. -/
theorem newton_terminal (n x : ℕ) (hx : 0 < x) (hstop : x ≤ (x + n / x) / 2) :
    x ≤ Nat.sqrt n := by
  apply Nat.le_sqrt.mpr
  have h := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mp hstop
  exact (Nat.le_div_iff_mul_le hx).mp (by omega)

end SampLib.IntegerSqrt
