module

public import SampLib.Latent.Laws.Interval

@[expose] public section

/-! # Sound comparisons and unresolved-interval bounds

The integer cross products are precisely the tests executed by the lazy oracle.
If neither test resolves, the two latent values lie within the combined width.
-/

namespace SampLib.LatentReal.RationalInterval

variable (a b : RationalInterval)

/-- The source's strict test is an endpoint comparison with positive denominators. -/
theorem strict_test_iff :
    a.upper * b.denominator < b.lower * a.denominator ↔ a.upperReal < b.lowerReal := by
  dsimp [upperReal, lowerReal]
  rw [div_lt_div_iff₀ a.denominatorReal_pos b.denominatorReal_pos]
  norm_cast

/-- The source's weak reverse test also handles exact equal point intervals. -/
theorem reverse_test_iff :
    b.upper * a.denominator ≤ a.lower * b.denominator ↔ b.upperReal ≤ a.lowerReal := by
  dsimp [upperReal, lowerReal]
  rw [div_le_div_iff₀ b.denominatorReal_pos a.denominatorReal_pos]
  norm_cast

theorem lt_of_strict_test {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y)
    (h : a.upper * b.denominator < b.lower * a.denominator) : x < y :=
  hx.2.trans_lt (((a.strict_test_iff b).mp h).trans_le hy.1)

theorem not_lt_of_reverse_test {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y)
    (h : b.upper * a.denominator ≤ a.lower * b.denominator) : ¬x < y :=
  not_lt_of_ge (hy.2.trans (((a.reverse_test_iff b).mp h).trans hx.1))

/-- Overlap makes the possible latent difference no larger than the combined widths. -/
theorem overlap_bound {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y)
    (hstrict : ¬a.upperReal < b.lowerReal) (hreverse : ¬b.upperReal ≤ a.lowerReal) :
    |x - y| ≤ a.width + b.width := by
  have hl := le_of_not_gt hstrict
  have hr := lt_of_not_ge hreverse
  apply abs_le.mpr
  constructor <;> dsimp [width] <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- An unresolved source comparison belongs to its measured uncertainty band. -/
theorem unresolved_error_le {x y ea eb : ℝ} (hx : a.Contains x) (hy : b.Contains y)
    (hstrict : ¬a.upper * b.denominator < b.lower * a.denominator)
    (hreverse : ¬b.upper * a.denominator ≤ a.lower * b.denominator)
    (ha : a.width ≤ ea) (hb : b.width ≤ eb) : |x - y| ≤ ea + eb :=
  (a.overlap_bound b hx hy ((a.strict_test_iff b).not.mp hstrict)
    ((a.reverse_test_iff b).not.mp hreverse)).trans (add_le_add ha hb)

end SampLib.LatentReal.RationalInterval
