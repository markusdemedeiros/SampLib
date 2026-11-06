import SampLib.Bernoulli.Laws.PiBoundsState
import SampLib.Bernoulli.Laws.EnclosureRatioLimits

/-! # Reciprocal π probabilities from positive Machin enclosures -/

namespace SampLib.ReciprocalPiProbability

noncomputable section

/-- The constant enclosure of a rational number. -/
def rational (numerator denominator : ℕ) (hd : 0 < denominator) :
    RealEnclosure.Interval ((numerator : ℝ) / denominator) where
  lower := numerator
  upper := numerator
  denominator := denominator
  positive := hd
  below := by
    push_cast
    rw [div_mul_cancel₀ _ (by exact_mod_cast hd.ne')]
  above := by
    push_cast
    rw [div_mul_cancel₀ _ (by exact_mod_cast hd.ne')]

theorem pi_left_pos (n : ℕ) : 0 < (PiBounds.interval n).left :=
  lt_trans (by norm_num) (PiBounds.interval_positive n)

def bias (numerator denominator : ℕ) (hd : 0 < denominator)
    (hp : (numerator : ℝ) ≤ denominator * Real.pi) : unitInterval :=
  ⟨numerator / (denominator * Real.pi), by positivity,
    (div_le_one (mul_pos (by exact_mod_cast hd) Real.pi_pos)).mpr hp⟩

def interval (numerator denominator : ℕ) (hd : 0 < denominator)
    (hp : (numerator : ℝ) ≤ denominator * Real.pi) (n : ℕ) :
    FromBounds.Interval (bias numerator denominator hd hp) :=
  ((rational numerator denominator hd).quotient (PiBounds.interval n)
    (by positivity) (pi_left_pos n)).toProbability _ (by simp [bias, div_div])

theorem tight (numerator denominator : ℕ) (hd : 0 < denominator)
    (hp : (numerator : ℝ) ≤ denominator * Real.pi) :
    FromBounds.Tight (interval numerator denominator hd hp) := by
  apply RealEnclosure.Tight.toProbability
  apply RealEnclosure.quotient_tight
  · simpa only [RealEnclosure.Interval.width, RealEnclosure.Interval.right,
      RealEnclosure.Interval.left, rational, sub_self] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) _ _)
  · exact PiBounds.interval_width_tendsto

end

end SampLib.ReciprocalPiProbability
