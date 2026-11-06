import SampLib.CoinComplement
import SampLib.Samplers.PLogInverse

/-! # The complementary logarithmic factory -/

open ProbLang
open scoped ENNReal

namespace SampLib.ComplementLogInverse

noncomputable section

private theorem complement_pos (p : unitInterval) (hp : (p : ℝ) < 1) :
    0 < (unitInterval.symm p : ℝ) := by
  simpa only [unitInterval.coe_symm_eq] using sub_pos.mpr hp

/-- The complementary logarithmic bias, with value zero at `p=0`. -/
def bias (p : unitInterval) (hp : (p : ℝ) < 1) : unitInterval :=
  PLogInverse.bias (unitInterval.symm p) (complement_pos p hp)

theorem bias_coe (p : unitInterval) (hp : (p : ℝ) < 1) :
    (bias p hp : ℝ) = (1 - (p : ℝ)) * Real.log (1 / (1 - (p : ℝ))) := by
  simp [bias, PLogInverse.bias, unitInterval.coe_symm_eq]

private theorem factory_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.FactoryExtra.pLogInverse = Occil.FactoryExtra.pLogInverse :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem factory_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.FactoryExtra.pLogInverse : Exp rT) =
      Occil.FactoryExtra.pLogInverse :=
  Exp.closeRec_fresh x _ k (by
    simp [Occil.FactoryExtra.pLogInverse, Occil.geometric, Exp.fv,
      RationalCoin.rationalCoin_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Apply the logarithmic factory to a fresh complemented input coin. -/
theorem twp_complementLogInverse (E : CoPset) (p : unitInterval) (hp : (p : ℝ) < 1)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (bias p hp)) -∗
      tglWp E pl(&Occil.FactoryExtra.complementLogInverse &coin.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iterate 2 twp_pure
  simp only [factory_open, factory_close]
  twp_bind pl(&Occil.FactoryExtra.pLogInverse &(CoinComplement.callback coin).fst #())
  iapply (tglWp_mono fun _ => tglWp_value)
  iapply (PLogInverse.twp_pLogInverse E (unitInterval.symm p) (complement_pos p hp)
    (CoinComplement.callback coin) (CoinComplement.distSpec E p coin hcoin) F)
  isimp only [RealCoin.lintegral_law, bias] at Hcredit
  iexact Hcredit

/-- Exact Bernoulli law throughout the terminating domain `p<1`. -/
theorem complementLogInverse_distSpec (E : CoPset) (p : unitInterval) (hp : (p : ℝ) < 1)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.complementLogInverse &coin.fst #())
      (RealCoin.law (bias p hp)) Val.bool where
  spec F _ := wand_entails (twp_complementLogInverse E p hp coin hcoin F)

end specification

end

end SampLib.ComplementLogInverse
