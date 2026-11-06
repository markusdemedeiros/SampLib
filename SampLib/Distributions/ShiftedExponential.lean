module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.UnitInterval

@[expose] public section

/-! # Probability parameters for shifted exponential factories -/

namespace SampLib.ShiftedExponential

noncomputable section

/-- The unit-interval exponential used by the concrete martingale gateway. -/
def unitBias (p : unitInterval) : unitInterval :=
  ⟨Real.exp (-(p : ℝ)), (Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr p.2.1)⟩

/-- Negative exponential of a nonnegative rational shift plus the input bias. -/
def bias (p : unitInterval) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) : unitInterval :=
  ⟨Real.exp (-((a : ℝ) / b + (p : ℝ))), (Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (add_nonneg
      (div_nonneg (by exact_mod_cast ha) (by exact_mod_cast hb.le)) p.2.1))⟩

/-- Independent rational and unit exponentials add their exponents. -/
theorem factor (p : unitInterval) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) :
    Real.exp (-(a : ℝ) / b) * (unitBias p : ℝ) = (bias p a b ha hb : ℝ) := by
  change Real.exp _ * Real.exp _ = Real.exp _
  rw [← Real.exp_add]
  congr 1
  ring

end

end SampLib.ShiftedExponential
