import SampLib.Uniform.Laws.RationalCoin

/-! # Integer urn proportions -/

open scoped ENNReal

namespace SampLib.Urn

noncomputable section

/-- The initial marked-ball fraction; the empty urn has an arbitrary zero bias. -/
def bias (ones zeros : ℕ) : unitInterval :=
  if h : 0 < ones + zeros then
    RationalCoin.bias ones (ones + zeros) (by omega) (by omega) (by omega)
  else 0

theorem pmf_true (ones zeros : ℕ) (h : 0 < ones + zeros) :
    RealCoin.pmf (bias ones zeros) true = (ones : ℝ≥0∞) / (ones + zeros) := by
  have hR : (0 : ℝ) < (ones : ℝ) + zeros := by exact_mod_cast h
  simp [bias, h, RealCoin.pmf, RationalCoin.bias, ENNReal.ofReal_div_of_pos hR,
    ENNReal.ofReal_add (Nat.cast_nonneg ones) (Nat.cast_nonneg zeros)]

theorem pmf_false (ones zeros : ℕ) (h : 0 < ones + zeros) :
    RealCoin.pmf (bias ones zeros) false = (zeros : ℝ≥0∞) / (ones + zeros) := by
  have hR : (0 : ℝ) < (ones : ℝ) + zeros := by exact_mod_cast h
  have hc : 1 - (ones : ℝ) / (ones + zeros) = zeros / (ones + zeros) := by
    field_simp
    ring
  simp [bias, h, RealCoin.pmf, RationalCoin.bias, hc, ENNReal.ofReal_div_of_pos hR,
    ENNReal.ofReal_add (Nat.cast_nonneg ones) (Nat.cast_nonneg zeros)]

end

end SampLib.Urn
