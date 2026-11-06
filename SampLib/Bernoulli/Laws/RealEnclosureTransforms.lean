import SampLib.Bernoulli.Laws.RealEnclosure

/-! # Limits and affine transformations of rational enclosures -/

open Filter
open scoped Topology

namespace SampLib.RealEnclosure

noncomputable section

variable {x : ℝ}

theorem left_tendsto (a : ℕ → Interval x)
    (h : Tendsto (fun n => (a n).width) atTop (𝓝 0)) :
    Tendsto (fun n => (a n).left) atTop (𝓝 x) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa using tendsto_const_nhds.sub h) tendsto_const_nhds
  · intro n
    have := (a n).le_right
    simp only [Interval.width] at *
    linarith
  · exact fun n => (a n).left_le

theorem right_tendsto (a : ℕ → Interval x)
    (h : Tendsto (fun n => (a n).width) atTop (𝓝 0)) :
    Tendsto (fun n => (a n).right) atTop (𝓝 x) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds (by simpa using tendsto_const_nhds.add h)
  · exact fun n => (a n).le_right
  · intro n
    have := (a n).left_le
    simp only [Interval.width] at *
    linarith

theorem Interval.lower_pos (a : Interval x) (h : 0 < a.left) : 0 < a.lower := by
  have hd : (0 : ℝ) < a.denominator := by exact_mod_cast a.positive
  have := (div_pos_iff_of_pos_right hd).mp h
  exact_mod_cast this

def Interval.affine (a : Interval x) (offset : ℤ) (divisor : ℕ) (hd : 0 < divisor) :
    Interval ((x - offset) / divisor) where
  lower := a.lower - offset * a.denominator
  upper := a.upper - offset * a.denominator
  denominator := divisor * a.denominator
  positive := Nat.mul_pos hd a.positive
  below := by
    have hd' : (divisor : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    rw [← mul_assoc, div_mul_cancel₀ _ hd']
    nlinarith [a.below]
  above := by
    have hd' : (divisor : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    rw [← mul_assoc, div_mul_cancel₀ _ hd']
    nlinarith [a.above]

@[simp] theorem Interval.affine_left (a : Interval x) (offset : ℤ) (divisor : ℕ)
    (hd : 0 < divisor) :
    (a.affine offset divisor hd).left = (a.left - offset) / divisor := by
  have ha : (a.denominator : ℝ) ≠ 0 := by exact_mod_cast a.positive.ne'
  have hd' : (divisor : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [Interval.left, Interval.affine]
  push_cast
  field_simp

@[simp] theorem Interval.affine_right (a : Interval x) (offset : ℤ) (divisor : ℕ)
    (hd : 0 < divisor) :
    (a.affine offset divisor hd).right = (a.right - offset) / divisor := by
  have ha : (a.denominator : ℝ) ≠ 0 := by exact_mod_cast a.positive.ne'
  have hd' : (divisor : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [Interval.right, Interval.affine]
  push_cast
  field_simp

@[simp] theorem Interval.affine_width (a : Interval x) (offset : ℤ) (divisor : ℕ)
    (hd : 0 < divisor) :
    (a.affine offset divisor hd).width = a.width / divisor := by
  simp only [Interval.width, Interval.affine_left, Interval.affine_right]
  ring

theorem Tight.affine {a : ℕ → Interval x} (h : Tight a)
    (offset : ℤ) (divisor : ℕ) (hd : 0 < divisor) :
    Tight (fun n => (a n).affine offset divisor hd) := by
  intro ε hε
  have hd' : (0 : ℝ) < divisor := by exact_mod_cast hd
  obtain ⟨n, hn⟩ := h (ε * divisor) (mul_pos hε hd')
  exact ⟨n, by simpa only [Interval.affine_width, div_le_iff₀ hd'] using hn⟩

end

end SampLib.RealEnclosure
