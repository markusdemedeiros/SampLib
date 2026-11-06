import SampLib.Constants.EulerScaledConstants
import SampLib.Bernoulli.ExpMinusScaled
import SampLib.Bernoulli.CoinProduct

/-! # An exponential coin from the unit-Poisson generating function -/

open ProbLang
open scoped ENNReal SampLib.ExponentialTerms

namespace SampLib.ExpDivThree

noncomputable section

abbrev poissonBias (p : unitInterval) : unitInterval :=
  ExpMinusScaled.bias (unitInterval.symm p) 1 1

abbrev bias (p : unitInterval) : unitInterval := EulerScaledConstants.third * poissonBias p

/-- The Poisson generating function cancels the prefactor `e/3`. -/
theorem bias_coe (p : unitInterval) : (bias p : ℝ) = Real.exp p / 3 := by
  simp only [bias, Set.Icc.coe_mul, EulerScaledConstants.third, EScaled.bias,
    poissonBias, ExpMinusScaled.bias, Nat.cast_one, Nat.cast_ofNat, mul_one, div_one,
    unitInterval.coe_symm_eq]
  rw [div_mul_eq_mul_div, ← Real.exp_add]
  congr 2
  ring

private theorem poisson_law (p : unitInterval) :
    ProbabilityGeneratingFactory.law (ProbabilityTheory.poissonMeasure 1) p =
      RealCoin.law (poissonBias p) := by
  simpa only [ExpMinusScaled.law, unitInterval.symm_symm,
    PoissonRational.rate, Nat.cast_one, div_one] using
    ExpMinusScaled.law_eq (unitInterval.symm p) 1 1

/-- One independent selector followed by the Poisson mixture preserves arbitrary credits. -/
theorem expectation (p : unitInterval) (F : Bool → ℝ≥0∞) :
    (∫⁻ r, CoinProduct.firstCredit (poissonBias p) F r
      ∂RealCoin.law EulerScaledConstants.third) = ∫⁻ r, F r ∂RealCoin.law (bias p) :=
  CoinProduct.expectation_preservation _ _ F

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

private instance scaled_closed : ClosedExp (Occil.Constants.eScaled : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.Constants.eScaled, Exp.fv, ClosedExp.closeRec, ClosedExp.fv]

private instance third_closed : ClosedExp (Occil.Constants.eDivThree : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.Constants.eDivThree, Exp.fv, ClosedExp.closeRec, ClosedExp.fv]

private instance pgf_closed : ClosedExp (Occil.probabilityGeneratingFactory : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.probabilityGeneratingFactory, Occil.iterateCoin, Exp.fv]

private instance poisson_closed : ClosedExp (Occil.poissonOne : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.poissonOne, Exp.fv, RndInt.rndInt_fv]

private def count : Val rT := ⟨pl(fun u, &Occil.poissonOne #()), .lam (by is_lc), by is_lc⟩

private theorem count_spec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&(count : Val rT).fst #())
      (ProbabilityTheory.poissonMeasure 1) (fun n : ℕ => Val.int (n : ℤ)) where
  spec F hF := by
    iintro Hcredit
    twp_pure
    iapply (PoissonOne.poissonOne_distSpec E).spec F hF $$ Hcredit

/-- No numerical evaluation of the unknown input probability occurs. -/
theorem twp_expDivThree (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ r, F r ∂RealCoin.law (bias p)) -∗
      tglWp E pl(&Occil.FactoryExtra.expDivThree &coin.fst #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  iintro Hcredit
  iterate 2 twp_pure
  twp_bind pl(&Occil.Constants.eDivThree #())
  isimp only [← expectation p F] at Hcredit
  iapply ((EulerScaledConstants.eDivThree_distSpec E).wp
    (CoinProduct.firstCredit (poissonBias p) F) (measurable_of_countable _) _) $$ Hcredit
  iintro %r Hcredit
  cases r
  · twp_pures
    twp_value
    imodintro
    iexists false
    isimp only [CoinProduct.firstCredit, Bool.false_eq_true, ite_false] at Hcredit
    iframe Hcredit
    itrivial
  · twp_pure
    isimp only [CoinProduct.firstCredit, ite_true] at Hcredit
    have hpgf := ProbabilityGeneratingFactory.probabilityGeneratingFactory_distSpec E
      (ProbabilityTheory.poissonMeasure 1) p coin count hcoin (count_spec E)
    have hsample := hpgf.spec F (measurable_of_countable _)
    simp only [poisson_law, count, Exp.close, Exp.closeRec, ClosedExp.closeRec] at hsample
    iapply hsample $$ Hcredit

theorem expDivThree_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.expDivThree &coin.fst #())
      (RealCoin.law (bias p)) Val.bool where
  spec F _ := wand_entails (twp_expDivThree E p coin hcoin F)

end specification

end

end SampLib.ExpDivThree
