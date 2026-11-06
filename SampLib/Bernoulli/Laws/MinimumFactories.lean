import SampLib.Bernoulli.Laws.MinimumComplementWalk
import SampLib.Bernoulli.CoinMean

/-! # The minimum and three-point piecewise-linear coin laws -/

namespace SampLib.MinimumComplement

noncomputable section

def bias (p : unitInterval) : unitInterval :=
  ⟨min (p : ℝ) (1 - p), le_min p.2.1 (sub_nonneg.mpr p.2.2),
    (min_le_left _ _).trans p.2.2⟩

theorem initial_bias (p : unitInterval) : Walk.bias (Walk.parameter p) 1 0 = bias p := by
  apply Subtype.ext
  exact Walk.initial p

def halfBias (p : unitInterval) : unitInterval :=
  ⟨min (p : ℝ) (1 / 2), le_min p.2.1 (by norm_num),
    (min_le_left _ _).trans p.2.2⟩

theorem mean_bias (p : unitInterval) : CoinMean.bias p (bias p) = halfBias p := by
  apply Subtype.ext
  change (1 - (1 / 2 : ℝ)) * min (p : ℝ) (1 - p) + (1 / 2 : ℝ) * p =
    min (p : ℝ) (1 / 2)
  by_cases hp : (p : ℝ) ≤ 1 / 2
  · rw [min_eq_left (by linarith), min_eq_left hp]
    ring
  · rw [min_eq_right (by linarith), min_eq_right (by linarith)]
    ring

/-- The six source constructions, indexed by their documented mode. -/
def piecewiseBias (p μ ν : unitInterval) : Fin 6 → unitInterval
  | 0 => CoinConditional.bias
      (CoinConditional.bias p (bias p) μ) 0 ν
  | 1 => CoinMean.bias (bias p)
      (CoinConditional.bias p (unitInterval.symm p) μ)
  | 2 => CoinConditional.bias (halfBias p) 0 μ
  | 3 => CoinConditional.bias (unitInterval.symm p) (bias p) μ
  | 4 => CoinConditional.bias (unitInterval.symm (bias p)) (unitInterval.symm p) μ
  | 5 => CoinConditional.bias (unitInterval.symm (bias p)) p μ

/-- Explicit piecewise-linear formulas, using the single hinge `min(p,1-p)`. -/
theorem piecewiseBias_coe (p μ ν : unitInterval) (mode : Fin 6) :
    (piecewiseBias p μ ν mode : ℝ) = match mode with
      | 0 => ν * ((1 - (μ : ℝ)) * min (p : ℝ) (1 - p) + μ * p)
      | 1 => (min (p : ℝ) (1 - p) + (1 - (μ : ℝ)) * (1 - p) + μ * p) / 2
      | 2 => μ * min (p : ℝ) (1 / 2)
      | 3 => (1 - (μ : ℝ)) * min (p : ℝ) (1 - p) + μ * (1 - p)
      | 4 => (1 - (μ : ℝ)) * (1 - p) + μ * (1 - min (p : ℝ) (1 - p))
      | 5 => (1 - (μ : ℝ)) * p + μ * (1 - min (p : ℝ) (1 - p)) := by
  fin_cases mode <;>
    simp [piecewiseBias, CoinConditional.bias, Set.Icc.coe_convexComb, bias, halfBias,
      unitInterval.coe_symm_eq, VonNeumann.fairBias]
  ring

end

end SampLib.MinimumComplement
