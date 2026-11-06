import SampLib.Samplers.SigmoidRational
import SampLib.Samplers.CoinProduct
import SampLib.Samplers.Complement

/-! # The logistic derivative coin -/

open Set ProbLang
open scoped ENNReal

namespace SampLib.SigmoidDerivative

noncomputable section

/-- Logistic success followed by an independent logistic failure. -/
def bias (a b : ℤ) : unitInterval :=
  SigmoidRational.bias a b * unitInterval.symm (SigmoidRational.bias a b)

def firstCredit (p : unitInterval) (F : Bool → ℝ≥0∞) (r : Bool) : ℝ≥0∞ :=
  if r then ∫⁻ q, F (!q) ∂RealCoin.law p else F false

/-- Independence multiplies the success probability by its complement. -/
theorem expectation (a b : ℤ) (F : Bool → ℝ≥0∞) :
    ∫⁻ r, firstCredit (SigmoidRational.bias a b) F r ∂RealCoin.law (SigmoidRational.bias a b) =
      ∫⁻ r, F r ∂RealCoin.law (bias a b) := by
  have hc : firstCredit (SigmoidRational.bias a b) F =
      CoinProduct.firstCredit (unitInterval.symm (SigmoidRational.bias a b)) F := by
    funext r
    cases r <;> simp [firstCredit, CoinProduct.firstCredit,
      Complement.expectation_preservation, Complement.law]
  rw [hc, CoinProduct.expectation_preservation]
  rfl

private theorem bool_not (r : Bool) : Bool.rec true false r = !r := by
  cases r <;> rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Two verified logistic draws, with the second complemented. -/
theorem twp_sigmoidDerivative (E : CoPset) (a b : ℤ) (hb : 0 < b)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ r, F r ∂RealCoin.law (bias a b)) -∗
      tglWp E pl(&Occil.FactoryExtra.sigmoidDerivative #int a #int b #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  iintro Hcredit
  iterate 3 twp_pure
  simp only [SigmoidRational.sigmoidRational_openRec, SigmoidRational.sigmoidRational_closeRec]
  twp_bind pl(&Occil.FactoryExtra.sigmoidRational #int a #int b #())
  isimp only [← expectation a b F] at Hcredit
  iapply ((SigmoidRational.sigmoidRational_distSpec E a b hb).wp
    (firstCredit (SigmoidRational.bias a b) F) (measurable_of_countable _) _) $$ Hcredit
  iintro %r Hcredit
  cases r
  · twp_pures
    twp_value
    imodintro
    iexists false
    isimp only [firstCredit, Bool.false_eq_true, ite_false] at Hcredit
    iframe Hcredit
    itrivial
  · twp_pure
    twp_bind pl(&Occil.FactoryExtra.sigmoidRational #int a #int b #())
    isimp only [firstCredit, ite_true] at Hcredit
    iapply ((SigmoidRational.sigmoidRational_distSpec E a b hb).wp
      (fun q => F (!q)) (measurable_of_countable _) _) $$ Hcredit
    iintro %q Hcredit
    twp_pures
    twp_value
    imodintro
    iexists !q
    iframe Hcredit
    ipureintro
    simp [Val.ext_iff, bool_not]

theorem sigmoidDerivative_distSpec (E : CoPset) (a b : ℤ) (hb : 0 < b) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.sigmoidDerivative #int a #int b #())
      (RealCoin.law (bias a b)) Val.bool where
  spec F _ := wand_entails (twp_sigmoidDerivative E a b hb F)

end specification

end

end SampLib.SigmoidDerivative
