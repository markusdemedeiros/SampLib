import SampLib.Uniform.RationalCoin

/-! # The capped rational acceptance test used by Metropolis kernels -/

open ProbLang
open scoped ENNReal

namespace SampLib.CappedRationalCoin

noncomputable section

def bias (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) : unitInterval :=
  ⟨min 1 ((a : ℝ) / b), le_min zero_le_one
    (div_nonneg (by exact_mod_cast ha) (by exact_mod_cast hb.le)), min_le_left _ _⟩

private theorem bias_full (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (h : b ≤ a) :
    bias a b ha hb = 1 := by
  apply Subtype.ext
  apply min_eq_left
  apply (le_div_iff₀ (by exact_mod_cast hb)).mpr
  simpa using (show (b : ℝ) ≤ a by exact_mod_cast h)

private theorem bias_fraction (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (h : a ≤ b) :
    bias a b ha hb = RationalCoin.bias a b ha hb h := by
  apply Subtype.ext
  exact min_eq_right ((div_le_one (by exact_mod_cast hb)).mpr (by exact_mod_cast h))

private theorem full_expectation (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (h : b ≤ a)
    (F : Bool → ℝ≥0∞) : ∫⁻ c, F c ∂RealCoin.law (bias a b ha hb) = F true := by
  rw [bias_full a b ha hb h]
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT] [ProbLangDist.IsUniformInt rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The saturation branch avoids calling the bounded coin outside its input domain. -/
theorem distSpec (E : CoPset) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) :
    IsDistSpec (GF := GF) E
      pl(if #int b <= #int a then #true else &Occil.rationalCoin #int a #int b)
      (RealCoin.law (bias a b ha hb)) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    by_cases h : b ≤ a
    · rw [decide_eq_true h]
      twp_pure
      twp_value
      imodintro
      iexists true
      isimp only [full_expectation a b ha hb h] at Hcredit
      iframe Hcredit
      itrivial
    · rw [decide_eq_false h]
      twp_pure
      have hab : a ≤ b := le_of_lt (lt_of_not_ge h)
      isimp only [bias_fraction a b ha hb hab] at Hcredit
      iapply ((RationalCoin.rationalCoin_distSpec E a b ha hb hab).wp F hF _) $$ Hcredit
      iintro %z Hcredit
      iexists z
      iframe Hcredit
      itrivial

end specification

end

end SampLib.CappedRationalCoin
