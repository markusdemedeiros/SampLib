module

public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Topology.UnitInterval

@[expose] public section

/-! # Algebraic constants in the unit interval -/

namespace SampLib.AlgebraicConstants

noncomputable section

/-- The inverse golden ratio, the root of `1-x-x²` in `(0,1)`. -/
def inverseGoldenBias : unitInterval :=
  ⟨Real.goldenRatio⁻¹, (inv_pos.mpr Real.goldenRatio_pos).le,
    (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio).le⟩

theorem inverseGoldenBias_pos : 0 < (inverseGoldenBias : ℝ) :=
  inv_pos.mpr Real.goldenRatio_pos

theorem inverseGoldenBias_lt_one : (inverseGoldenBias : ℝ) < 1 :=
  inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio

theorem inverseGoldenBias_equation :
    (inverseGoldenBias : ℝ) ^ 2 + (inverseGoldenBias : ℝ) = 1 := by
  change Real.goldenRatio⁻¹ ^ 2 + Real.goldenRatio⁻¹ = 1
  rw [Real.inv_goldenRatio]
  nlinarith [Real.goldenConj_sq]

/-- The root of `x²+2x-1` in `(0,1)`. -/
def sqrtTwoMinusOneBias : unitInterval :=
  ⟨Real.sqrt 2 - 1, sub_nonneg.mpr Real.one_lt_sqrt_two.le,
    by have := (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)).mpr (by norm_num : (2 : ℝ) < 2 ^ 2)
       linarith⟩

theorem sqrtTwoMinusOneBias_pos : 0 < (sqrtTwoMinusOneBias : ℝ) :=
  sub_pos.mpr Real.one_lt_sqrt_two

theorem sqrtTwoMinusOneBias_lt_one : (sqrtTwoMinusOneBias : ℝ) < 1 := by
  have := (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)).mpr (by norm_num : (2 : ℝ) < 2 ^ 2)
  dsimp [sqrtTwoMinusOneBias]
  linarith

theorem sqrtTwoMinusOneBias_equation :
    (sqrtTwoMinusOneBias : ℝ) ^ 2 + 2 * (sqrtTwoMinusOneBias : ℝ) = 1 := by
  dsimp [sqrtTwoMinusOneBias]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The positive root of `2x²-1`. -/
def inverseSqrtTwoBias : unitInterval :=
  ⟨(Real.sqrt 2)⁻¹, (inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))).le,
    (inv_lt_one_of_one_lt₀ Real.one_lt_sqrt_two).le⟩

theorem inverseSqrtTwoBias_pos : 0 < (inverseSqrtTwoBias : ℝ) :=
  inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))

theorem inverseSqrtTwoBias_lt_one : (inverseSqrtTwoBias : ℝ) < 1 :=
  inv_lt_one_of_one_lt₀ Real.one_lt_sqrt_two

theorem inverseSqrtTwoBias_equation : 2 * (inverseSqrtTwoBias : ℝ) ^ 2 = 1 := by
  change 2 * (Real.sqrt 2)⁻¹ ^ 2 = 1
  rw [inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

end

end SampLib.AlgebraicConstants
