import SampLib.Bernoulli.Support.LatentPower
import SampLib.Bernoulli.Laws.LogarithmicMean
import SampLib.Bernoulli.SampleGeometricBag
import SampLib.Common.CoinComplement
import SampLib.Core.Syntax.ClosedExp
import Samplers.Bernoulli.Elementary

/-! # The logarithmic-ratio factories

A single cached uniform supplies the shared exponent in `p^U`. Averaging its
conditional power law gives the logarithmic mean, with its endpoint extension.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LogRatioFactories

noncomputable section

abbrev complementBias (p : unitInterval) (hp : 0 < (p : ℝ)) := LogarithmicMean.bias p hp

private theorem complemented_positive (p : unitInterval) (hp : (p : ℝ) < 1) :
    0 < (unitInterval.symm p : ℝ) := by
  simpa only [unitInterval.coe_symm_eq] using sub_pos.mpr hp

abbrev overLogBias (p : unitInterval) (hp : (p : ℝ) < 1) :=
  LogarithmicMean.bias (unitInterval.symm p) (complemented_positive p hp)

/-- The singular point is filled by the continuous extension. -/
theorem complementBias_coe (p : unitInterval) (hp : 0 < (p : ℝ)) :
    (complementBias p hp : ℝ) =
      if (p : ℝ) = 1 then 1 else (1 - (p : ℝ)) / Real.log (1 / (p : ℝ)) := by
  rw [LogarithmicMean.bias_coe]
  by_cases h : (p : ℝ) = 1
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]
    simp only [one_div, Real.log_inv, div_neg]
    ring

/-- Complementing the base gives the second logarithmic-ratio formula. -/
theorem overLogBias_coe (p : unitInterval) (hp : (p : ℝ) < 1) :
    (overLogBias p hp : ℝ) =
      if (p : ℝ) = 0 then 1 else (p : ℝ) / Real.log (1 / (1 - (p : ℝ))) := by
  rw [LogarithmicMean.bias_coe]
  by_cases h : (p : ℝ) = 0
  · have hs : (unitInterval.symm p : ℝ) = 1 := by simp [unitInterval.coe_symm_eq, h]
    rw [ite_eq_left hs, ite_eq_left h]
  · have hs : (unitInterval.symm p : ℝ) ≠ 1 := by
      rw [unitInterval.coe_symm_eq]
      intro heq
      apply h
      linarith
    rw [ite_eq_right hs, ite_eq_right h, unitInterval.coe_symm_eq]
    simp only [one_div, Real.log_inv, div_neg]
    ring

@[simp] theorem complementBias_one :
    (complementBias 1 (by norm_num) : ℝ) = 1 := by simp [complementBias_coe]

@[simp] theorem overLogBias_zero :
    (overLogBias 0 (by norm_num) : ℝ) = 1 := by simp [overLogBias_coe]

private theorem posterior_const (q : List Bool) (c : ℝ≥0∞) :
    DyadicPosterior.credit q (fun _ => c) = c := by simp [DyadicPosterior.credit]

private instance twoCoinPower_closed {rT : Type} :
    ClosedExp (Occil.FactoryExtra.twoCoinPower : Exp rT) where
  lc := by is_lc
  fv := by
    rw [TwoCoinPower.Program.source_eq]
    simp [TwoCoinPower.Program.sourceCode, Exp.fv, RationalCoin.rationalCoin_fv]

private instance geometricBag_closed {rT : Type} :
    ClosedExp (Occil.sampleGeometricBag : Exp rT) where
  lc := by is_lc
  fv := by
    simp [Occil.sampleGeometricBag, Occil.uniformBagStep, Occil.newUniformBag,
      Exp.fv, FairCoin.fairCoin_fv]

private instance newBag_closed {rT : Type} : ClosedExp (Occil.newUniformBag : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.newUniformBag, Exp.fv]

private def exponentCoin {rT : Type} (l : Loc) : Val rT :=
  ⟨.lam (.app (.app Occil.sampleGeometricBag (.lit (.loc l))) (.lit .unit)),
    .lam (by is_lc), by is_lc⟩

private def complementSource {rT : Type} : Val rT :=
  ⟨Occil.FactoryExtra.complementOverLogInverse, .lam (by is_lc), by is_lc⟩

private def overLogSource {rT : Type} : Val rT :=
  ⟨Occil.FactoryExtra.pOverLogInverseComplement, .lam (by is_lc), by is_lc⟩

private theorem complementSource_fst {rT : Type} :
    (complementSource : Val rT).fst = Occil.FactoryExtra.complementOverLogInverse := rfl

private theorem overLogSource_fst {rT : Type} :
    (overLogSource : Val rT).fst = Occil.FactoryExtra.pOverLogInverseComplement := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

private theorem exponent_spec (E : CoPset) (l : Loc) :
    UniformBag.IsCoinSpec (GF := GF) E l pl(&(exponentCoin l : Val rT).fst #())
      LatentBernoulli.bias where
  measurable_bias := LatentBernoulli.measurable_bias
  spec q G hG := by
    iintro ⟨Hbag, Hcredit⟩
    twp_pure
    iapply (SampleGeometricBag.sampleGeometricBag_coinSpec E l).spec q G hG
    iframe Hbag Hcredit

private theorem twp_power (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (base : Val rT)
    (hbase : IsDistSpec (GF := GF) E pl(&base.fst #()) (RealCoin.law p) Val.bool)
    (l : Loc) (F : Bool → ℝ≥0∞) :
    iprop(UniformBag.owns l [] ∗ ↯ (RealCoin.credit (LogarithmicMean.bias p hp) F)) ⊢
      tglWp E pl(&Occil.FactoryExtra.twoCoinPower &base.fst &(exponentCoin l).fst #())
        (fun v : Val rT => iprop(∃ bit : Bool, ⌜v = Val.bool bit⌝ ∗ ↯ (F bit))) := by
  iintro ⟨Hbag, Hcredit⟩
  isimp only [← LogarithmicMean.expectation p hp F] at Hcredit
  iapply ((LatentPower.twoCoinPower_coinSpec E p hp LatentBernoulli.bias base
    (exponentCoin l) l hbase (exponent_spec E l)).wp [] (fun b _ => F b)
    (fun _ => measurable_const) _) $$ Hbag Hcredit
  iintro %bit %q - Hbag Hcredit
  isimp only [posterior_const] at Hcredit
  iexists bit
  iframe Hcredit
  itrivial

/-- `(1-p)/log(1/p)`, with value one at `p=1`, for the complete documented domain `p>0`. -/
theorem complementOverLogInverse_distSpec (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.complementOverLogInverse &coin.fst #())
      (RealCoin.law (complementBias p hp)) Val.bool where
  spec F _ := by
    iintro Hcredit
    rw [← complementSource_fst (rT := rT)]
    iterate 2 twp_pure
    twp_bind pl(&Occil.newUniformBag #())
    iapply tglWp_wand
    isplitl []
    · iapply UniformBag.twp_newUniformBag E
    iintro %v ⟨%l, %hv, Hbag⟩
    subst v
    twp_pure
    ieval (
      change _ ⊢ tglWp E
        pl(&Occil.FactoryExtra.twoCoinPower &coin.fst &(exponentCoin l).fst #()) _)
    isimp only [RealCoin.lintegral_law] at Hcredit
    iapply twp_power E p hp coin hcoin l F
    iframe Hbag Hcredit

/-- `p/log(1/(1-p))`, with value one at `p=0`, for the complete documented domain `p<1`. -/
theorem pOverLogInverseComplement_distSpec (E : CoPset) (p : unitInterval) (hp : (p : ℝ) < 1)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.pOverLogInverseComplement &coin.fst #())
      (RealCoin.law (overLogBias p hp)) Val.bool where
  spec F _ := by
    iintro Hcredit
    rw [← overLogSource_fst (rT := rT)]
    iterate 2 twp_pure
    twp_bind pl(&Occil.newUniformBag #())
    iapply tglWp_wand
    isplitl []
    · iapply UniformBag.twp_newUniformBag E
    iintro %v ⟨%l, %hv, Hbag⟩
    subst v
    twp_pure
    ieval (
      change _ ⊢ tglWp E pl(&Occil.FactoryExtra.twoCoinPower
        &(CoinComplement.callback coin).fst &(exponentCoin l).fst #()) _)
    isimp only [RealCoin.lintegral_law] at Hcredit
    iapply twp_power E (unitInterval.symm p) (complemented_positive p hp)
      (CoinComplement.callback coin)
      (CoinComplement.distSpec E p coin hcoin) l F
    iframe Hbag Hcredit

end specification

end

end SampLib.LogRatioFactories
