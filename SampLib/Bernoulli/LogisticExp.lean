import SampLib.Bernoulli.SigmoidRational
import SampLib.Bernoulli.Support.FactoryIntegerPower

/-! # Logistic coins at binary precision -/

open Set ProbLang
open scoped ENNReal

namespace SampLib.LogisticExp

noncomputable section

/-- The input is negated and divided by the exact power-of-two scale. -/
def bias (z : ℤ) (precision : ℕ) : unitInterval :=
  SigmoidRational.bias (-z) (2 ^ precision)

/-- Explicit logistic complement at binary precision. -/
theorem coe_bias (z : ℤ) (precision : ℕ) :
    (bias z precision : ℝ) = 1 / (1 + Real.exp ((z : ℝ) / 2 ^ precision)) := by
  simp [bias, SigmoidRational.bias]

@[local simp] private theorem power_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.FactoryExtra.intPower = Occil.FactoryExtra.intPower :=
  (Exp.open_lc k e _ (by is_lc)).symm

@[local simp] private theorem power_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.FactoryExtra.intPower : Exp rT) = Occil.FactoryExtra.intPower :=
  Exp.closeRec_fresh x _ k (by simp [Occil.FactoryExtra.intPower, Exp.fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Compute the scale and delegate to the signed rational logistic coin. -/
theorem twp_logisticExp (E : CoPset) (z : ℤ) (precision : ℕ) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ r, F r ∂RealCoin.law (bias z precision)) -∗
      tglWp E pl(&Occil.FactoryExtra.logisticExp #int z #int (precision : ℤ) #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  iintro Hcredit
  iterate 5 twp_pure
  simp only [power_open, power_close, SigmoidRational.sigmoidRational_openRec,
    SigmoidRational.sigmoidRational_closeRec]
  twp_bind pl(&Occil.FactoryExtra.intPower #2 #int (precision : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply FactoryIntegerPower.twp_intPower E 2 precision
  iintro %v %hv
  subst v
  twp_pure
  isimp only [Exp.ofVal]
  isimp only [bias] at Hcredit
  iapply (SigmoidRational.sigmoidRational_distSpec E (-z) (2 ^ precision)
    (pow_pos (by decide : (0 : ℤ) < 2) precision)).spec F (measurable_of_countable _) $$ Hcredit

theorem logisticExp_distSpec (E : CoPset) (z : ℤ) (precision : ℕ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.logisticExp #int z #int (precision : ℤ) #())
      (RealCoin.law (bias z precision)) Val.bool where
  spec F _ := wand_entails (twp_logisticExp E z precision F)

end specification

end

end SampLib.LogisticExp
