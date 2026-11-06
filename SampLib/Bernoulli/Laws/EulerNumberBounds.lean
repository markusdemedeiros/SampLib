import SampLib.Bernoulli.Laws.EulerEnclosure

/-! # Elementary bounds for Euler's number from the factorial enclosure -/

namespace SampLib.EulerNumber

noncomputable section

theorem exp_one_gt_two : 2 < Real.exp 1 := by
  have h := EulerEnclosure.lower_bound 2
  norm_num [EulerEnclosure.numerator] at h
  linarith

theorem exp_one_lt_three : Real.exp 1 < 3 := by
  have h := EulerEnclosure.upper_bound 2 (by decide)
  norm_num [EulerEnclosure.numerator] at h
  linarith

end

end SampLib.EulerNumber
