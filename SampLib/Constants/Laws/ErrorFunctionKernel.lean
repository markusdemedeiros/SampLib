module

public import SampLib.Constants.Laws.SquaredDecreasing
public import SampLib.Common.Laws.AcceptedProposal

@[expose] public section

/-! # The Gaussian integral behind the error-function ratio -/

open Set MeasureTheory Real ProbLang
open ENNReal (ofReal)
open LawfulProbLangℝ (unifUnit)
open scoped ENNReal

namespace SampLib.ErrorFunctionKernel

noncomputable section

/-- The Gaussian integral whose common scaling cancels in `erf(x)/erf(1)`. -/
def integral (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, exp (-t ^ 2)

def erf (x : ℝ) : ℝ := (2 / sqrt Real.pi) * integral x

theorem integral_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ integral x :=
  intervalIntegral.integral_nonneg hx (fun _ _ => (exp_pos _).le)

theorem mass_eq : AcceptedProposal.mass unifUnit SquaredDecreasing.decay =
    ofReal (integral 1) := by
  change (∫⁻ t in Icc (0 : ℝ) 1, ofReal (exp (-t ^ 2))) = _
  rw [ProbLang.TotalEris.Examples.lintegral_ofReal_Icc zero_le_one (by fun_prop)
    (fun _ _ => (exp_pos _).le)]
  rfl

theorem window_mass (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    ∫⁻ t in Iio x, AcceptedProposal.weight SquaredDecreasing.decay t ∂unifUnit =
      ofReal (integral x) := by
  change (∫⁻ t, ofReal (exp (-t ^ 2)) ∂(volume.restrict (Icc (0 : ℝ) 1)).restrict (Iio x)) = _
  have hs : Iio x ∩ Icc (0 : ℝ) 1 = Ico 0 x := by
    ext t
    simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.le.trans hx.2⟩⟩
  rw [Measure.restrict_restrict measurableSet_Iio, hs, restrict_Ico_eq_restrict_Icc,
    ProbLang.TotalEris.Examples.lintegral_ofReal_Icc hx.1 (by fun_prop)
      (fun _ _ => (exp_pos _).le)]
  rfl

theorem ratio_eq (x : ℝ) : integral x / integral 1 = erf x / erf 1 := by
  rw [erf, erf, mul_div_mul_left _ _ (by positivity : (2 / sqrt Real.pi : ℝ) ≠ 0)]

end

end SampLib.ErrorFunctionKernel
