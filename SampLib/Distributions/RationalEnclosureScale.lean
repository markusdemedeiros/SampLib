import SampLib.Distributions.RealEnclosure

/-! # Scaling a real enclosure by a nonnegative rational -/

namespace SampLib.RealEnclosure

noncomputable section

def Interval.scale {x : ℝ} (a : Interval x) (u v : ℕ) (hv : 0 < v) :
    Interval (x * u / v) where
  lower := u * a.lower
  upper := u * a.upper
  denominator := v * a.denominator
  positive := Nat.mul_pos hv a.positive
  below := by
    have hv' : (v : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left a.below (Nat.cast_nonneg u)]
  above := by
    have hv' : (v : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left a.above (Nat.cast_nonneg u)]

theorem Interval.scale_width {x : ℝ} (a : Interval x) (u v : ℕ) (hv : 0 < v) :
    (a.scale u v hv).width = ((u : ℝ) / v) * a.width := by
  simp only [Interval.width, Interval.left, Interval.right, Interval.scale]
  push_cast
  ring

theorem Tight.scale {x : ℝ} {a : ℕ → Interval x} (h : Tight a)
    (u v : ℕ) (hv : 0 < v) : Tight (fun n => (a n).scale u v hv) := by
  intro ε hε
  by_cases hu : u = 0
  · exact ⟨0, by simp [Interval.scale_width, hu, hε.le]⟩
  · have hc : (0 : ℝ) < (u : ℝ) / v := by positivity
    obtain ⟨n, hn⟩ := h (ε / ((u : ℝ) / v)) (by positivity)
    refine ⟨n, ?_⟩
    rw [Interval.scale_width]
    simpa only [mul_comm] using (le_div_iff₀ hc).mp hn

end

end SampLib.RealEnclosure
