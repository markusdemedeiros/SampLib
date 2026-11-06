module

public import SampLib.Distributions.AlgebraicConstants

@[expose] public section

namespace SampLib.GoldenFamily

noncomputable section

/-- The two quadratic families with their root strictly between zero and one. -/
structure Parameters where
  m : ℕ
  ell : ℤ
  positive : 0 < m
  unit : ell = 1 ∨ ell = -1
  minus : ell = -1 → 3 ≤ m

/-- `G(m,ell) = (m + sqrt(m²+4ell))/2`. -/
def shape (a : Parameters) : ℝ :=
  ((a.m : ℝ) + Real.sqrt ((a.m : ℝ) ^ 2 + 4 * (a.ell : ℝ))) / 2

private theorem discriminant_nonneg (a : Parameters) :
    0 ≤ (a.m : ℝ) ^ 2 + 4 * (a.ell : ℝ) := by
  rcases a.unit with h | h
  · rw [h]
    positivity
  · have hm : (3 : ℝ) ≤ a.m := by exact_mod_cast a.minus h
    rw [h]
    norm_num
    nlinarith [sq_nonneg ((a.m : ℝ) - 3)]

theorem shape_gt_one (a : Parameters) : 1 < shape a := by
  have hm : (1 : ℝ) ≤ a.m := by exact_mod_cast a.positive
  rcases a.unit with h | h
  · have hr : (a.m : ℝ) < Real.sqrt ((a.m : ℝ) ^ 2 + 4) :=
      Real.lt_sqrt_of_sq_lt (by linarith)
    dsimp [shape]
    rw [h]
    norm_num
    linarith
  · have hm3 : (3 : ℝ) ≤ a.m := by exact_mod_cast a.minus h
    have hd : 0 < (a.m : ℝ) ^ 2 - 4 := by
      nlinarith [sq_nonneg ((a.m : ℝ) - 3)]
    have hr := Real.sqrt_pos.mpr hd
    simp only [sub_eq_add_neg] at hr
    dsimp [shape]
    rw [h]
    norm_num
    linarith

theorem shape_equation (a : Parameters) :
    shape a ^ 2 - a.m * shape a - a.ell = 0 := by
  have hr := Real.sq_sqrt (discriminant_nonneg a)
  dsimp [shape]
  nlinarith

/-- The inverse quadratic root; finite products give the requested negative powers. -/
def bias (a : Parameters) : unitInterval :=
  ⟨(shape a)⁻¹, (inv_pos.mpr (lt_trans zero_lt_one (shape_gt_one a))).le,
    (inv_lt_one_of_one_lt₀ (shape_gt_one a)).le⟩

theorem bias_pos (a : Parameters) : 0 < (bias a : ℝ) :=
  inv_pos.mpr (lt_trans zero_lt_one (shape_gt_one a))

theorem bias_lt_one (a : Parameters) : (bias a : ℝ) < 1 :=
  inv_lt_one_of_one_lt₀ (shape_gt_one a)

theorem bias_equation (a : Parameters) :
    (a.ell : ℝ) * (bias a : ℝ) ^ 2 + (a.m : ℝ) * (bias a : ℝ) = 1 := by
  change (a.ell : ℝ) * (shape a)⁻¹ ^ 2 + (a.m : ℝ) * (shape a)⁻¹ = 1
  have hn : shape a ≠ 0 := (lt_trans zero_lt_one (shape_gt_one a)).ne'
  field_simp [hn]
  nlinarith [shape_equation a]

end

end SampLib.GoldenFamily
