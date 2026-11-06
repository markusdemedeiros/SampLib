import SampLib.Distributions.EnclosureRatioLimits

open Filter
open scoped Topology

namespace SampLib.RealEnclosure

private def zeroInterval : Interval 0 where
  lower := 0
  upper := 0
  denominator := 1
  positive := by decide
  below := by norm_num
  above := by norm_num

private def oneInterval : Interval 1 where
  lower := 1
  upper := 1
  denominator := 1
  positive := by decide
  below := by norm_num
  above := by norm_num

-- A zero numerator is allowed; only the denominator must stay positive.
example : Tight (fun _ : ℕ => zeroInterval.quotient oneInterval (by norm_num)
    (by norm_num [oneInterval, Interval.left])) := by
  apply quotient_tight (fun _ => zeroInterval) (fun _ => oneInterval)
  · simp [zeroInterval, Interval.width, Interval.left, Interval.right]
  · simp [oneInterval, Interval.width, Interval.left, Interval.right]

#print axioms quotient_width_tendsto
#print axioms quotient_tight

end SampLib.RealEnclosure
