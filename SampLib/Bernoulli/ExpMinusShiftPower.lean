import SampLib.Bernoulli.Support.ShiftPowerCore
import SampLib.Bernoulli.ExpMinusMartingale
import Samplers.Bernoulli.Exponential

/-! # The shifted-power negative-exponential factory

The concrete martingale factory supplies exp(-p^i). Its finite repetitions form
exactly the binomial factors of exp(-(m+p)^k), including k=0 and m=0.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.ExpMinusShiftPower

noncomputable section

abbrev bias := BinomialShiftPower.bias

theorem bias_coe (p : unitInterval) (m k : ℕ) :
    (bias p m k : ℝ) = Real.exp (-(((m : ℝ) + p) ^ k)) := rfl

private def exponentialSampler {rT : Type} : Val rT :=
  ⟨Occil.expMinusMartingale, .lam ExpMinusMartingale.expMinusMartingale_lc,
    ExpMinusMartingale.expMinusMartingale_lc⟩

private theorem exponentialSampler_fst {rT : Type} :
    (exponentialSampler : Val rT).fst = Occil.expMinusMartingale := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem sampler_spec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) (i : ℕ) :
    IsDistSpec (GF := GF) E
      pl(&exponentialSampler.fst &(ShiftPowerCore.powerCoin coin i).fst #())
      (RealCoin.law (ShiftedExponential.unitBias (IterateCoin.bias p i))) Val.bool := by
  have hb : FactorialSeriesFactory.bias .exp (IterateCoin.bias p i) =
      ShiftedExponential.unitBias (IterateCoin.bias p i) := by
    apply Subtype.ext
    exact FactorialSeriesFactory.bias_exp_coe _
  have h := ExpMinusMartingale.expMinusMartingale_distSpec E (IterateCoin.bias p i)
    (ShiftPowerCore.powerCoin coin i) (ShiftPowerCore.powerCoin_distSpec E p coin hcoin i)
  simpa only [exponentialSampler_fst, hb] using h

/-- Instantiate the checked binomial-product loop with the concrete martingale sampler. -/
theorem twp_expMinusShiftPower (E : CoPset) (p : unitInterval) (m k : ℕ) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (bias p m k)) -∗
      tglWp E pl(&Occil.FactoryExtra.expMinusShiftPower &coin.fst
        #int (m : ℤ) #int (k : ℤ) #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  unfold Occil.FactoryExtra.expMinusShiftPower
  simp only [Exp.close, Exp.closeRec, ExpMinusMartingale.expMinusMartingale_closeRec,
    FactorySyntax.iterateCoin_closeRec, FactoryChoose.choose_closeRec,
    ShiftPowerCore.intPower_closeRec]
  rw [← exponentialSampler_fst (rT := rT)]
  iintro Hcredit
  iterate 9 twp_pure
  isimp only [FactorySyntax.iterateCoin_openRec, FactoryChoose.choose_openRec,
    ShiftPowerCore.intPower_openRec]
  ieval (
    change _ ⊢ tglWp E pl(&(ShiftPowerCore.loop coin exponentialSampler m k) #0) _)
  have hloop := ShiftPowerCore.twp_loop E p coin exponentialSampler
    (sampler_spec E p coin hcoin) m k 0 (k + 1) (by simp) F
  simp only [BinomialShiftPower.tail_zero] at hloop
  iapply hloop $$ Hcredit

/-- Exact exp(-(m+p)^k) for every m,k≥0 and every input bias p∈[0,1]. -/
theorem expMinusShiftPower_distSpec (E : CoPset) (p : unitInterval) (m k : ℕ) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.expMinusShiftPower &coin.fst
      #int (m : ℤ) #int (k : ℤ) #()) (RealCoin.law (bias p m k)) Val.bool where
  spec F _ := wand_entails (twp_expMinusShiftPower E p m k coin hcoin F)

end specification

end

end SampLib.ExpMinusShiftPower
