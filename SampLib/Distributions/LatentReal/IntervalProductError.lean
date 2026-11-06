module

public import SampLib.Distributions.LatentReal.Interval

@[expose] public section

/-! # Product-enclosure error at a shared latent point

A corner differs from the latent product by two linear errors and their product.
The bound is pointwise and permits two aliases of the same latent operand.
-/

namespace SampLib.LatentReal.RationalInterval

variable (a b : RationalInterval)

/-- Two values in one enclosure differ by at most its width. -/
theorem abs_sub_le_width {x y : ℝ} (hx : a.Contains x) (hy : a.Contains y) :
    |x - y| ≤ a.width := by
  apply abs_le.mpr
  constructor <;> dsimp [width] <;> linarith [hx.1, hx.2, hy.1, hy.2]

private theorem corner_error {x y u v ea eb : ℝ}
    (hu : |u - x| ≤ ea) (hv : |v - y| ≤ eb) :
    |u * v - x * y| ≤ ea * |y| + |x| * eb + ea * eb := by
  have hea : 0 ≤ ea := (abs_nonneg _).trans hu
  have hdecomp : u * v - x * y = (u - x) * y + x * (v - y) + (u - x) * (v - y) := by ring
  rw [hdecomp]
  calc
    _ ≤ |(u - x) * y + x * (v - y)| + |(u - x) * (v - y)| := abs_add_le _ _
    _ ≤ |(u - x) * y| + |x * (v - y)| + |(u - x) * (v - y)| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ = |u - x| * |y| + |x| * |v - y| + |u - x| * |v - y| := by
      simp only [abs_mul]
    _ ≤ ea * |y| + |x| * eb + ea * eb :=
      add_le_add
        (add_le_add (mul_le_mul_of_nonneg_right hu (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hv (abs_nonneg _)))
        (mul_le_mul hu hv (abs_nonneg _) hea)

/-- Four-corner multiplication has a vanishing error whenever its operands do. -/
theorem width_multiply_le {x y ea eb : ℝ} (hx : a.Contains x) (hy : b.Contains y)
    (ha : a.width ≤ ea) (hb : b.width ≤ eb) :
    (a.multiply b).width ≤ 2 * (ea * |y| + |x| * eb + ea * eb) := by
  let error := ea * |y| + |x| * eb + ea * eb
  have hcorner {u v : ℝ} (hu : a.Contains u) (hv : b.Contains v) :
      x * y - error ≤ u * v ∧ u * v ≤ x * y + error := by
    have h := abs_le.mp (corner_error ((a.abs_sub_le_width hu hx).trans ha)
      ((b.abs_sub_le_width hv hy).trans hb))
    constructor <;> dsimp [error] <;> linarith [h.1, h.2]
  have hll := hcorner ⟨le_rfl, a.lowerReal_le_upperReal⟩ ⟨le_rfl, b.lowerReal_le_upperReal⟩
  have hlu := hcorner ⟨le_rfl, a.lowerReal_le_upperReal⟩ ⟨b.lowerReal_le_upperReal, le_rfl⟩
  have hul := hcorner ⟨a.lowerReal_le_upperReal, le_rfl⟩ ⟨le_rfl, b.lowerReal_le_upperReal⟩
  have huu := hcorner ⟨a.lowerReal_le_upperReal, le_rfl⟩ ⟨b.lowerReal_le_upperReal, le_rfl⟩
  have hlo : x * y - error ≤ (a.multiply b).lowerReal := by
    rw [lowerReal_multiply]
    exact le_min (le_min hll.1 hlu.1) (le_min hul.1 huu.1)
  have hhi : (a.multiply b).upperReal ≤ x * y + error := by
    rw [upperReal_multiply]
    exact max_le (max_le hll.2 hlu.2) (max_le hul.2 huu.2)
  change (a.multiply b).upperReal - (a.multiply b).lowerReal ≤ 2 * error
  linarith

end SampLib.LatentReal.RationalInterval
