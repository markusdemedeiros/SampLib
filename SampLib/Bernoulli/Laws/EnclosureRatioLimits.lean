import SampLib.Bernoulli.Laws.EnclosureRatio
import SampLib.Bernoulli.Laws.RealEnclosureTransforms

/-! # Shrinking quotient enclosures -/

open Filter
open scoped Topology

namespace SampLib.RealEnclosure

noncomputable section

variable {x y : ℝ}

/-- Both quotient endpoints converge to the same ratio when the denominator stays positive. -/
theorem quotient_width_tendsto (a : ℕ → Interval x) (b : ℕ → Interval y)
    (hx : 0 ≤ x) (hb : ∀ n, 0 < (b n).left)
    (ha : Tendsto (fun n => (a n).width) atTop (𝓝 0))
    (hw : Tendsto (fun n => (b n).width) atTop (𝓝 0)) :
    Tendsto (fun n => ((a n).quotient (b n) hx (hb n)).width) atTop (𝓝 0) := by
  have hy : y ≠ 0 := ne_of_gt ((hb 0).trans_le (b 0).left_le)
  simpa only [Interval.width, Interval.quotient_right, Interval.quotient_left,
    Pi.div_apply, sub_self]
    using ((right_tendsto a ha).div (left_tendsto b hw) hy).sub
      ((left_tendsto a ha).div (right_tendsto b hw) hy)

theorem quotient_tight (a : ℕ → Interval x) (b : ℕ → Interval y)
    (hx : 0 ≤ x) (hb : ∀ n, 0 < (b n).left)
    (ha : Tendsto (fun n => (a n).width) atTop (𝓝 0))
    (hw : Tendsto (fun n => (b n).width) atTop (𝓝 0)) :
    Tight (fun n => (a n).quotient (b n) hx (hb n)) :=
  Tight.of_tendsto _ (quotient_width_tendsto a b hx hb ha hw)

end

end SampLib.RealEnclosure
