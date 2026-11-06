import SampLib.Distributions.EnclosureRatioLimits
import SampLib.Distributions.EulerEnclosure
import SampLib.Distributions.PiBoundsState

/-! # The canonical Euler-to-pi probability and its concrete rational enclosures -/

namespace SampLib.EulerPi

noncomputable section

private theorem pi_positive : 0 < Real.pi :=
  (show (0 : ℝ) < 3 by norm_num).trans
    ((PiBounds.interval_positive 0).trans_le (PiBounds.interval 0).left_le)

private theorem exp_le_three : Real.exp 1 ≤ 3 := by
  simpa [RealEnclosure.Interval.right, EulerEnclosure.interval, EulerEnclosure.numerator]
    using (EulerEnclosure.interval 0).le_right

def bias : unitInterval := ⟨Real.exp 1 / Real.pi,
  (div_pos (Real.exp_pos _) pi_positive).le,
  (div_le_one pi_positive).mpr (exp_le_three.trans
    ((PiBounds.interval_positive 0).le.trans (PiBounds.interval 0).left_le))⟩

def interval (n : ℕ) : RealEnclosure.Interval (Real.exp 1 / Real.pi) :=
  (EulerEnclosure.interval n).quotient (PiBounds.interval n) (Real.exp_pos _).le
    ((show (0 : ℝ) < 3 by norm_num).trans (PiBounds.interval_positive n))

theorem interval_triple (n : ℕ) : (interval n).triple =
    ((EulerEnclosure.interval n).lower * ((PiBounds.interval n).denominator : ℤ) *
      (PiBounds.interval n).lower,
     ((EulerEnclosure.interval n).upper * ((PiBounds.interval n).denominator : ℤ) *
       (PiBounds.interval n).upper,
      ((EulerEnclosure.interval n).denominator : ℤ) * (PiBounds.interval n).lower *
        (PiBounds.interval n).upper)) :=
  RealEnclosure.Interval.quotient_triple _ _ _ _

theorem tight : RealEnclosure.Tight interval :=
  RealEnclosure.quotient_tight EulerEnclosure.interval PiBounds.interval
    (Real.exp_pos _).le
    (fun n => (show (0 : ℝ) < 3 by norm_num).trans (PiBounds.interval_positive n))
    EulerEnclosure.width_tendsto PiBounds.interval_width_tendsto

end

end SampLib.EulerPi
