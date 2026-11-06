module

public import SampLib.Common.Laws.FractionalPower

@[expose] public section

/-! # Quotient/remainder factorization of a nonnegative rational power -/

namespace SampLib.RationalPower

noncomputable section

/-- Integer and fractional trials multiply to the original rational exponent. -/
theorem power_split {p : ℝ} (hp : 0 ≤ p) (a b : ℕ) (hb : 0 < b) :
    p ^ (a / b) * p ^ ((a % b : ℕ) / (b : ℝ) : ℝ) = p ^ ((a : ℝ) / b : ℝ) := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hsplit : (a : ℝ) / b = ((a / b : ℕ) : ℝ) + (a % b : ℕ) / (b : ℝ) := by
    apply (div_eq_iff hbR).mpr
    rw [add_mul, div_mul_cancel₀ _ hbR]
    exact_mod_cast (by simpa only [Nat.mul_comm] using (Nat.div_add_mod a b).symm :
      a = a / b * b + a % b)
  rw [hsplit, Real.rpow_add_of_nonneg hp (by positivity) (by positivity), Real.rpow_natCast]

end

end SampLib.RationalPower
