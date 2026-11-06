import SampLib.Uniform.Laws.RationalCoin

/-! # Capped rational acceptance bias

Saturating at one keeps the bounded rational coin inside its input domain.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.CappedRationalCoin

noncomputable section

def bias (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) : unitInterval :=
  ⟨min 1 ((a : ℝ) / b), le_min zero_le_one
    (div_nonneg (by exact_mod_cast ha) (by exact_mod_cast hb.le)), min_le_left _ _⟩

theorem bias_full (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (h : b ≤ a) :
    bias a b ha hb = 1 := by
  apply Subtype.ext
  apply min_eq_left
  apply (le_div_iff₀ (by exact_mod_cast hb)).mpr
  simpa using (show (b : ℝ) ≤ a by exact_mod_cast h)

theorem bias_fraction (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (h : a ≤ b) :
    bias a b ha hb = RationalCoin.bias a b ha hb h := by
  apply Subtype.ext
  exact min_eq_right ((div_le_one (by exact_mod_cast hb)).mpr (by exact_mod_cast h))

theorem full_expectation (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (h : b ≤ a)
    (F : Bool → ℝ≥0∞) : ∫⁻ c, F c ∂RealCoin.law (bias a b ha hb) = F true := by
  rw [bias_full a b ha hb h]
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]

end

end SampLib.CappedRationalCoin
