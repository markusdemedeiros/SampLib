import SampLib.Samplers.OneDivOnePlus
import SampLib.CoinComplement
import Samplers.Bernoulli.Rational

/-! # The reciprocal factory `1/(2-p)` -/

open Set ProbLang
open scoped ENNReal

namespace SampLib.OneDivTwoMinus

noncomputable section

/-- Complement the input of the reciprocal factory. -/
def bias (p : unitInterval) : unitInterval := OneDivOnePlus.bias (unitInterval.symm p)

theorem bias_coe (p : unitInterval) : (bias p : ℝ) = 1 / (2 - (p : ℝ)) := by
  simp only [bias, OneDivOnePlus.bias, EvenParity.bias, unitInterval.coe_symm_eq]
  congr 1
  ring

@[simp] private theorem reciprocal_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.oneDivOnePlus = Occil.oneDivOnePlus :=
  (Exp.open_lc k e _ (by is_lc)).symm

@[simp] private theorem reciprocal_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.oneDivOnePlus : Exp rT) = Occil.oneDivOnePlus :=
  Exp.closeRec_fresh x _ k (by simp [Occil.oneDivOnePlus, Exp.fv, FairCoin.fairCoin_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The reciprocal construction accepts every input bias, including zero and one. -/
theorem twp_oneDivTwoMinus (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (bias p)) -∗
      tglWp E pl(&Occil.FactoryExtra.oneDivTwoMinus &coin.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iterate 2 twp_pure
  simp only [reciprocal_open, reciprocal_close]
  twp_bind pl(&Occil.oneDivOnePlus &(CoinComplement.callback coin).fst #())
  iapply (tglWp_mono fun _ => tglWp_value)
  iapply (OneDivOnePlus.twp_oneDivOnePlus E (unitInterval.symm p) (CoinComplement.callback coin)
    (CoinComplement.distSpec E p coin hcoin) F)
  isimp only [RealCoin.lintegral_law, bias] at Hcredit
  iexact Hcredit

/-- Typed Bernoulli law with bias `1/(2-p)`. -/
theorem oneDivTwoMinus_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.oneDivTwoMinus &coin.fst #())
      (RealCoin.law (bias p)) Val.bool where
  spec F _ := wand_entails (twp_oneDivTwoMinus E p coin hcoin F)

end specification

end

end SampLib.OneDivTwoMinus
