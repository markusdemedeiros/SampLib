module

public import SampLib.Distributions.LatentReal.Interval
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Lattice

@[expose] public section

/-! # Convergent enclosures and shared latent arithmetic

Precision schedules need not be dyadic after arithmetic. It is enough that the
intervals enclose one fixed value and their widths tend to zero.
-/

open Filter Topology

namespace SampLib.LatentReal.RationalInterval

/-- An enclosure schedule retains its value while its uncertainty vanishes. -/
def Approximates (intervals : ℕ → RationalInterval) (x : ℝ) : Prop :=
  (∀ n, (intervals n).Contains x) ∧
    Tendsto (fun n => (intervals n).width) atTop (𝓝 0)

namespace Approximates

variable {intervals other : ℕ → RationalInterval} {x y : ℝ}

theorem lowerReal_tendsto (h : Approximates intervals x) :
    Tendsto (fun n => (intervals n).lowerReal) atTop (𝓝 x) := by
  have hlo : Tendsto (fun n => x - (intervals n).width) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.sub h.2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds ?_ ?_
  · intro n
    have hn := (h.1 n).2
    dsimp [width]
    linarith
  · exact fun n => (h.1 n).1

theorem upperReal_tendsto (h : Approximates intervals x) :
    Tendsto (fun n => (intervals n).upperReal) atTop (𝓝 x) := by
  have hhi : Tendsto (fun n => x + (intervals n).width) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.add h.2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hhi ?_ ?_
  · exact fun n => (h.1 n).2
  · intro n
    have hn := (h.1 n).1
    dsimp [width]
    linarith

/-- All observations identify one latent real, even without a nested precision schedule. -/
theorem unique (h : Approximates intervals x) (k : Approximates intervals y) : x = y :=
  tendsto_nhds_unique h.lowerReal_tendsto k.lowerReal_tendsto

theorem negate (h : Approximates intervals x) :
    Approximates (fun n => (intervals n).negate) (-x) := by
  refine ⟨fun n => contains_negate _ (h.1 n), ?_⟩
  simpa only [width_negate] using h.2

theorem add (h : Approximates intervals x) (k : Approximates other y) :
    Approximates (fun n => (intervals n).add (other n)) (x + y) := by
  refine ⟨fun n => contains_add _ _ (h.1 n) (k.1 n), ?_⟩
  simpa only [width_add, add_zero] using h.2.add k.2

/-- The four corner limits agree, even when the two operands share randomness. -/
theorem multiply (h : Approximates intervals x) (k : Approximates other y) :
    Approximates (fun n => (intervals n).multiply (other n)) (x * y) := by
  have haa := h.lowerReal_tendsto.mul k.lowerReal_tendsto
  have hab := h.lowerReal_tendsto.mul k.upperReal_tendsto
  have hba := h.upperReal_tendsto.mul k.lowerReal_tendsto
  have hbb := h.upperReal_tendsto.mul k.upperReal_tendsto
  have hlo : Tendsto (fun n => ((intervals n).multiply (other n)).lowerReal)
      atTop (𝓝 (x * y)) := by
    simpa only [lowerReal_multiply, min_self] using (haa.min hab).min (hba.min hbb)
  have hhi : Tendsto (fun n => ((intervals n).multiply (other n)).upperReal)
      atTop (𝓝 (x * y)) := by
    simpa only [upperReal_multiply, max_self] using (haa.max hab).max (hba.max hbb)
  exact ⟨fun n => contains_multiply _ _ (h.1 n) (k.1 n),
    by simpa only [width, sub_self] using hhi.sub hlo⟩

/-- Fixed rational scaling transports the same latent value and its shrinking enclosure. -/
theorem scaleRational (h : Approximates intervals x) (numerator denominator : ℤ)
    (hd : 0 < denominator) :
    Approximates (fun n => (intervals n).scaleRational numerator denominator hd)
      (x * (numerator / denominator)) := by
  have hlo : Tendsto (fun n =>
      ((intervals n).scaleRational numerator denominator hd).lowerReal)
      atTop (𝓝 (x * (numerator / denominator))) := by
    by_cases hn : numerator < 0
    · simpa only [lowerReal_scaleRational, ite_eq_left hn] using
        h.upperReal_tendsto.mul_const ((numerator : ℝ) / denominator)
    · simpa only [lowerReal_scaleRational, ite_eq_right hn] using
        h.lowerReal_tendsto.mul_const ((numerator : ℝ) / denominator)
  have hhi : Tendsto (fun n =>
      ((intervals n).scaleRational numerator denominator hd).upperReal)
      atTop (𝓝 (x * (numerator / denominator))) := by
    by_cases hn : numerator < 0
    · simpa only [upperReal_scaleRational, ite_eq_left hn] using
        h.lowerReal_tendsto.mul_const ((numerator : ℝ) / denominator)
    · simpa only [upperReal_scaleRational, ite_eq_right hn] using
        h.upperReal_tendsto.mul_const ((numerator : ℝ) / denominator)
  exact ⟨fun n => contains_scaleRational _ numerator denominator hd (h.1 n),
    by simpa only [width, sub_self] using hhi.sub hlo⟩

/-- Distinct latent values eventually have disjoint observable intervals. -/
theorem eventually_below (h : Approximates intervals x) (k : Approximates other y)
    (hxy : x < y) :
    ∀ᶠ n in atTop, (intervals n).upperReal < (other n).lowerReal :=
  h.upperReal_tendsto.eventually_lt k.lowerReal_tendsto hxy

/-- A nonzero latent value eventually has a zero-separated interval. -/
theorem eventually_separated (h : Approximates intervals x) (hx : x ≠ 0) :
    ∀ᶠ n in atTop, 0 < (intervals n).lower ∨ (intervals n).upper < 0 := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · filter_upwards [h.upperReal_tendsto.eventually_lt tendsto_const_nhds hx] with n hn
    right
    have hi : ((intervals n).upper : ℝ) < 0 := by
      simpa only [zero_mul] using (div_lt_iff₀ (intervals n).denominatorReal_pos).mp hn
    exact_mod_cast hi
  · filter_upwards [tendsto_const_nhds.eventually_lt h.lowerReal_tendsto hx] with n hn
    left
    have hi : (0 : ℝ) < (intervals n).lower := by
      simpa only [zero_mul] using (lt_div_iff₀ (intervals n).denominatorReal_pos).mp hn
    exact_mod_cast hi

/-- Once separated from zero, reciprocal enclosures converge to the same inverse. -/
theorem reciprocal (h : Approximates intervals x) (hx : x ≠ 0)
    (hzero : ∀ n, 0 < (intervals n).lower ∨ (intervals n).upper < 0) :
    Approximates (fun n => (intervals n).reciprocal (hzero n)) (1 / x) := by
  have hlo : Tendsto (fun n => ((intervals n).reciprocal (hzero n)).lowerReal)
      atTop (𝓝 (1 / x)) := by
    simpa only [lowerReal_reciprocal, one_div] using h.upperReal_tendsto.inv₀ hx
  have hhi : Tendsto (fun n => ((intervals n).reciprocal (hzero n)).upperReal)
      atTop (𝓝 (1 / x)) := by
    simpa only [upperReal_reciprocal, one_div] using h.lowerReal_tendsto.inv₀ hx
  exact ⟨fun n => contains_reciprocal _ (hzero n) (h.1 n),
    by simpa only [width, sub_self] using hhi.sub hlo⟩

end Approximates

end SampLib.LatentReal.RationalInterval
