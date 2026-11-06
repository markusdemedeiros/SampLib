module

public import SampLib.Common.Laws.FractionalPower

@[expose] public section

/-! # Nonnegative rational powers of a bias

The quotient and remainder of `a / b` split `p^(a/b)` into integer and fractional trials.
-/

namespace SampLib.RationalPower

noncomputable section

/-- The Bernoulli bias for a nonnegative rational power. -/
def bias (p : unitInterval) (a b : ℕ) (_hb : 0 < b) : unitInterval :=
  ⟨(p : ℝ) ^ ((a : ℝ) / b : ℝ), Real.rpow_nonneg p.2.1 _,
    Real.rpow_le_one p.2.1 p.2.2 (by positivity)⟩

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
