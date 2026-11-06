import SampLib.Samplers.SigmoidRational
import SampLib.Samplers.CoinConditional

/-! # An exponential-ratio coin -/

open Set ProbLang
open scoped ENNReal

namespace SampLib.ExponentialRatio

noncomputable section

/-- The exponential coin is selected by a logistic coin; otherwise return true. -/
def bias (a b x y : ℤ) (hx : 0 ≤ x) (hy : 0 < y) : unitInterval :=
  CoinConditional.bias (ExpMinusRational.bias x y hx hy) 1 (SigmoidRational.bias a b)

/-- The conditional mixture has bias `(1+exp(z-w))/(1+exp(z))`. -/
theorem coe_bias (a b x y : ℤ) (hx : 0 ≤ x) (hy : 0 < y) :
    (bias a b x y hx hy : ℝ) =
      (1 + Real.exp ((a : ℝ) / b - (x : ℝ) / y)) / (1 + Real.exp ((a : ℝ) / b)) := by
  have he : Real.exp (-(a : ℝ) / b) * Real.exp ((a : ℝ) / b) = 1 := by
    rw [← Real.exp_add,
      show -(a : ℝ) / b + (a : ℝ) / b = 0 by ring, Real.exp_zero]
  simp only [bias, CoinConditional.bias, Set.Icc.convexComb, ExpMinusRational.bias,
    SigmoidRational.bias, Set.Icc.coe_one, Real.exp_sub, Real.exp_neg, neg_div]
  field_simp
  nlinarith

def firstCredit (x y : ℤ) (hx : 0 ≤ x) (hy : 0 < y)
    (F : Bool → ℝ≥0∞) (r : Bool) : ℝ≥0∞ :=
  if r then ∫⁻ q, F q ∂RealCoin.law (ExpMinusRational.bias x y hx hy) else F true

/-- Condition on the logistic selector to obtain the ratio's expectation. -/
theorem expectation (a b x y : ℤ) (hx : 0 ≤ x) (hy : 0 < y)
    (F : Bool → ℝ≥0∞) :
    ∫⁻ r, firstCredit x y hx hy F r ∂RealCoin.law (SigmoidRational.bias a b) =
      ∫⁻ r, F r ∂RealCoin.law (bias a b x y hx hy) := by
  have hc : firstCredit x y hx hy F =
      CoinConditional.firstCredit (ExpMinusRational.bias x y hx hy) 1 F := by
    funext r
    cases r <;> simp [firstCredit, CoinConditional.firstCredit,
      RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]
  rw [hc, CoinConditional.expectation_preservation]
  rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Execute one selector and, on success, one exponential draw. -/
theorem twp_exponentialRatio (E : CoPset) (a b x y : ℤ) (hb : 0 < b)
    (hx : 0 ≤ x) (hy : 0 < y) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ r, F r ∂RealCoin.law (bias a b x y hx hy)) -∗
      tglWp E pl(&Occil.FactoryExtra.exponentialRatio #int a #int b #int x #int y #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  iintro Hcredit
  iterate 5 twp_pure
  simp only [SigmoidRational.sigmoidRational_openRec, SigmoidRational.sigmoidRational_closeRec,
    ExpMinusRational.expMinusRational_openRec, ExpMinusRational.expMinusRational_closeRec]
  twp_bind pl(&Occil.FactoryExtra.sigmoidRational #int a #int b #())
  isimp only [← expectation a b x y hx hy F] at Hcredit
  iapply ((SigmoidRational.sigmoidRational_distSpec E a b hb).wp
    (firstCredit x y hx hy F) (measurable_of_countable _) _) $$ Hcredit
  iintro %r Hcredit
  cases r
  · twp_pures
    twp_value
    imodintro
    iexists true
    isimp only [firstCredit, Bool.false_eq_true, ite_false] at Hcredit
    iframe Hcredit
    itrivial
  · twp_pure
    isimp only [firstCredit, ite_true] at Hcredit
    iapply (ExpMinusRational.expMinusRational_distSpec E x y hx hy).spec F
      (measurable_of_countable _) $$ Hcredit

theorem exponentialRatio_distSpec (E : CoPset) (a b x y : ℤ) (hb : 0 < b)
    (hx : 0 ≤ x) (hy : 0 < y) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.exponentialRatio #int a #int b #int x #int y #())
      (RealCoin.law (bias a b x y hx hy)) Val.bool where
  spec F _ := wand_entails (twp_exponentialRatio E a b x y hb hx hy F)

end specification

end

end SampLib.ExponentialRatio
