module

public import SampLib.Discrete.Laws.DyadicBlocks
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! # Cancellation of dyadic proposal and power acceptance weights -/

namespace SampLib.DyadicBlocks

/-- A geometric level weight cancels the corresponding block power. -/
theorem power_cancel (r : ℝ) (l : ℕ) :
    ((2 : ℝ) ^ (1 - r)) ^ l * ((2 : ℝ) ^ l) ^ r = (2 : ℝ) ^ l := by
  rw [← Real.rpow_mul_natCast (by norm_num) (1 - r) l,
    ← Real.rpow_natCast_mul (by norm_num) l r,
    ← Real.rpow_add (by norm_num)]
  rw [show (1 - r) * (l : ℝ) + (l : ℝ) * r = (l : ℝ) by ring]
  simp

/-- Uniform rank and power acceptance leave just the target negative power. -/
theorem cancellation (r : ℝ) (l : ℕ) (v : ℝ) (hv : 0 < v) :
    (((2 : ℝ) ^ (1 - r)) ^ l / (2 : ℝ) ^ l) * (((2 : ℝ) ^ l) / v) ^ r = v ^ (-r) := by
  rw [Real.div_rpow (by positivity) hv.le, div_mul_div_comm, power_cancel,
    ← div_div, div_self (by positivity), Real.rpow_neg hv.le, one_div]

end SampLib.DyadicBlocks
