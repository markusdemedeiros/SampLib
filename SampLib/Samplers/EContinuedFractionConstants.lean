import SampLib.Samplers.EContinuedFraction
import SampLib.Distributions.EulerContinuedFraction
import SampLib.Samplers.InverseEPlusRational
import SampLib.Distributions.EulerConstants

/-! # Euler's continued-fraction identities at the two constant-coin entry points -/

open ProbLang

namespace SampLib.EContinuedFractionConstants

noncomputable section

private theorem ratio_ge_one (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) : 1 ≤ (a : ℝ) / b := by
  apply (le_div_iff₀ (by exact_mod_cast hb)).mpr
  simpa only [one_mul] using (show (b : ℝ) ≤ a by exact_mod_cast hab)

private theorem coefficient_eq (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) :
    RationalContinuedFraction.sequence (EContinuedFraction.coefficients a b hb hab) =
      EulerContinuedFraction.coefficient ((a : ℝ) / b) (ratio_ge_one a b hb hab) := by
  funext j
  by_cases h0 : j = 0
  · subst j
    simp [RationalContinuedFraction.sequence, RationalContinuedFraction.Coefficient.real,
      EContinuedFraction.coefficients, EContinuedFraction.denominator, EContinuedFraction.scale,
      EulerContinuedFraction.coefficient, EulerContinuedFraction.partialQuotient]
  by_cases h1 : j = 1
  · subst j
    have hb' : (b : ℝ) ≠ 0 := by positivity
    simp [RationalContinuedFraction.sequence, RationalContinuedFraction.Coefficient.real,
      EContinuedFraction.coefficients, EContinuedFraction.denominator, EContinuedFraction.scale,
      EulerContinuedFraction.coefficient, hb']
  · simp [RationalContinuedFraction.sequence, RationalContinuedFraction.Coefficient.real,
      EContinuedFraction.coefficients, EContinuedFraction.denominator, EContinuedFraction.scale,
      EulerContinuedFraction.coefficient, EulerContinuedFraction.partialQuotient, h0, h1]

/-- Euler's positive integral remainders identify the second continued-fraction tail. -/
theorem bias_two (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) :
    (EContinuedFraction.bias a b hb hab 2 : ℝ) = Real.exp 1 - 2 := by
  simpa only [EContinuedFraction.bias, RationalContinuedFraction.value, coefficient_eq] using
    EulerContinuedFraction.value_two ((a : ℝ) / b) (ratio_ge_one a b hb hab)

/-- Replacing the first denominator by `a/b` shifts the reciprocal of Euler's number. -/
theorem bias_one (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) :
    (EContinuedFraction.bias a b hb hab 1 : ℝ) = 1 / (Real.exp 1 + (a : ℝ) / b - 2) := by
  simpa only [EContinuedFraction.bias, RationalContinuedFraction.value, coefficient_eq] using
    EulerContinuedFraction.value_one ((a : ℝ) / b) (ratio_ge_one a b hb hab)

private theorem inverse_bias_eq (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) :
    EContinuedFraction.bias a b hb hab 1 = InverseEPlusRational.bias a b hb hab :=
  Subtype.ext (bias_one a b hb hab)

private theorem minus_two_bias_eq :
    EContinuedFraction.bias 1 1 (by decide) (by decide) 2 = EulerConstants.minusTwo :=
  Subtype.ext (bias_two 1 1 (by decide) (by decide))

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

/-- The actual continued-fraction wrapper at every rational shift `a/b ≥ 1`. -/
theorem inverseEPlusContinuedFraction_distSpec (E : CoPset) (a b : ℕ)
    (hb : 0 < b) (hab : b ≤ a) :
    IsDistSpec (GF := GF) E
      pl(&Occil.Constants.inverseEPlusContinuedFraction #int (a : ℤ) #int (b : ℤ) #())
      (RealCoin.law (InverseEPlusRational.bias a b hb hab)) Val.bool where
  spec F hF := by
    iintro Hcredit
    iterate 3 twp_pure
    have hsample := (EContinuedFraction.eContinuedFraction_distSpec (rT := rT) (GF := GF) E
      a b 1 hb hab (by decide)).spec F hF
    simp only [inverse_bias_eq] at hsample
    iapply hsample $$ Hcredit

/-- The alternate continued-fraction expansion samples `e-2`. -/
theorem eMinusTwoContinuedFraction_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.eMinusTwoContinuedFraction #())
      (RealCoin.law EulerConstants.minusTwo) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    have hsample := (EContinuedFraction.eContinuedFraction_distSpec (rT := rT) (GF := GF) E 1 1 2
      (by decide) (by decide) (by decide)).spec F hF
    simp only [minus_two_bias_eq] at hsample
    iapply hsample $$ Hcredit

end specification

end

end SampLib.EContinuedFractionConstants
