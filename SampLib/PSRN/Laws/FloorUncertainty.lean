module

public import SampLib.Latent.Laws.Interval
public import SampLib.Latent.Laws.ComparisonUncertainty
public import Mathlib.MeasureTheory.Function.Floor

@[expose] public section

/-! # Integer-grid uncertainty for exact deferred floors

Away from the integer grid, a sufficiently narrow enclosure lies inside one floor
cell. The distance to that cell's nearest boundary measures the unresolved mass.
-/

open MeasureTheory Set

namespace SampLib.LatentFloorUncertainty

noncomputable section

/-- Distance from a real to the nearer boundary of its current floor cell. -/
def margin (x : ℝ) : ℝ := min (x - ⌊x⌋) (⌊x⌋ + 1 - x)

@[fun_prop] theorem measurable_margin : Measurable margin := by
  unfold margin
  fun_prop

theorem margin_nonneg (x : ℝ) : 0 ≤ margin x :=
  le_min (sub_nonneg.mpr (Int.floor_le x)) (sub_nonneg.mpr (Int.lt_floor_add_one x).le)

theorem margin_pos {x : ℝ} (hx : x ≠ (⌊x⌋ : ℤ)) : 0 < margin x := by
  exact lt_min (sub_pos.mpr (lt_of_le_of_ne (Int.floor_le x) (Ne.symm hx)))
    (sub_pos.mpr (Int.lt_floor_add_one x))

end

end SampLib.LatentFloorUncertainty

namespace SampLib.LatentReal.RationalInterval

open SampLib.LatentFloorUncertainty

/-- The exact lower integer quotient executed by `floorScaled`. -/
def lowerFloor (I : RationalInterval) (scale : ℤ) : ℤ := I.lower * scale / I.denominator

def upperFloor (I : RationalInterval) (scale : ℤ) : ℤ := I.upper * scale / I.denominator

theorem lowerFloor_eq (I : RationalInterval) (scale : ℤ) :
    I.lowerFloor scale = ⌊I.lowerReal * scale⌋ := by
  rw [lowerReal, div_mul_eq_mul_div, ← Int.cast_mul,
    Int.floor_div_cast_of_nonneg I.denominator_pos.le, Int.floor_intCast]
  rfl

theorem upperFloor_eq (I : RationalInterval) (scale : ℤ) :
    I.upperFloor scale = ⌊I.upperReal * scale⌋ := by
  rw [upperReal, div_mul_eq_mul_div, ← Int.cast_mul,
    Int.floor_div_cast_of_nonneg I.denominator_pos.le, Int.floor_intCast]
  rfl

/-- Equal endpoint quotients determine the latent integer without revealing the real. -/
theorem floor_eq_of_resolved (I : RationalInterval) {x : ℝ} (hx : I.Contains x)
    {scale : ℤ} (hscale : 0 ≤ scale) (h : I.lowerFloor scale = I.upperFloor scale) :
    ⌊x * scale⌋ = I.lowerFloor scale := by
  have hk : (0 : ℝ) ≤ scale := by exact_mod_cast hscale
  have hlo := Int.floor_mono (mul_le_mul_of_nonneg_right hx.1 hk)
  have hhi := Int.floor_mono (mul_le_mul_of_nonneg_right hx.2 hk)
  rw [← lowerFloor_eq] at hlo
  rw [← upperFloor_eq, ← h] at hhi
  exact le_antisymm hhi hlo

/-- Different endpoint quotients place the latent real in the grid uncertainty band. -/
theorem unresolved_margin_le (I : RationalInterval) {x : ℝ} (hx : I.Contains x)
    {scale : ℤ} (hscale : 0 ≤ scale) (h : I.lowerFloor scale ≠ I.upperFloor scale) :
    margin (x * scale) ≤ I.width * scale := by
  by_contra! hnarrow
  change I.width * scale < min (x * scale - (⌊x * scale⌋ : ℝ))
    ((⌊x * scale⌋ : ℝ) + 1 - x * scale) at hnarrow
  have hk : (0 : ℝ) ≤ scale := by exact_mod_cast hscale
  have hlo := mul_le_mul_of_nonneg_right hx.1 hk
  have hhi := mul_le_mul_of_nonneg_right hx.2 hk
  have hwidth : I.upperReal * scale - I.lowerReal * scale = I.width * scale := by
    dsimp [width]
    ring
  have hl := min_le_left (x * scale - (⌊x * scale⌋ : ℝ))
    ((⌊x * scale⌋ : ℝ) + 1 - x * scale)
  have hr := min_le_right (x * scale - (⌊x * scale⌋ : ℝ))
    ((⌊x * scale⌋ : ℝ) + 1 - x * scale)
  have hcell_lower : ⌊I.lowerReal * scale⌋ = ⌊x * scale⌋ := by
    apply Int.floor_eq_iff.mpr
    constructor <;> linarith
  have hcell_upper : ⌊I.upperReal * scale⌋ = ⌊x * scale⌋ := by
    apply Int.floor_eq_iff.mpr
    constructor <;> linarith
  exact h (by rw [lowerFloor_eq, upperFloor_eq, hcell_lower, hcell_upper])

end SampLib.LatentReal.RationalInterval
