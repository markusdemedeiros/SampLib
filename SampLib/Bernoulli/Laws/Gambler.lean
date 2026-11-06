import SampLib.Bernoulli.Laws.FiniteGeometricWalk
import SampLib.Bernoulli.Laws.LogisticFactory

/-! # Laws of the finite gambler's-ruin factory

The walk steps down with the logistic probability of the ratio `ap/b`. Its success law is
the normalized geometric tail of that ratio.
-/

namespace SampLib.Gambler

noncomputable section

abbrev ratio (p : unitInterval) (a b : ℤ) : ℝ := (a : ℝ) * p / b

theorem ratio_nonneg (p : unitInterval) (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    0 ≤ ratio p a b :=
  div_nonneg (mul_nonneg (by exact_mod_cast ha.le) p.2.1) (by exact_mod_cast hb.le)

theorem logistic_bias (p : unitInterval) (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    LogisticFactory.integerBias p a b ha hb =
      FiniteGeometricWalk.down (ratio p a b) (ratio_nonneg p a b ha hb) := by
  apply Subtype.ext
  change (a : ℝ) * p / ((b : ℝ) + a * p) =
    ((a : ℝ) * p / b) / (1 + (a : ℝ) * p / b)
  have hd : 0 < (b : ℝ) + a * (p : ℝ) :=
    add_pos_of_pos_of_nonneg (by exact_mod_cast hb)
      (mul_nonneg (by exact_mod_cast ha.le) p.2.1)
  field_simp [(show (b : ℝ) ≠ 0 by exact_mod_cast hb.ne'), hd.ne']

/-- Geometric-tail hitting probability, with height zero interpreted as an immediate upper exit. -/
def bias (p : unitInterval) (a b : ℤ) (ha : 0 < a) (hb : 0 < b) (height : ℕ) :
    unitInterval :=
  FiniteGeometricWalk.bias (ratio p a b) (ratio_nonneg p a b ha hb)
    (max height 1) (by omega) 1

end

end SampLib.Gambler
