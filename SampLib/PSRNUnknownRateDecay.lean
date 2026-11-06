import SampLib.PSRNDecayCoins
import SampLib.Samplers.ExpMinusFactory
import SampLib.BetaStep

/-! # The unknown-rate exponential's actual decay callback -/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNUnknownRateDecay

noncomputable section

def body {rT : Type} (coin : Val rT) : Exp rT :=
  .app (.app Occil.expMinusFactory
    (.lam (.cond (.app coin.fst (.lit .unit))
      (.app (.app Occil.rationalCoin (.lit (.int 1))) (.bvar 1)) (.lit (.bool false)))))
    (.lit .unit)

/-- The divisor is observed at each call; the unknown probability stays in the supplied coin. -/
def value {rT : Type} (coin : Val rT) : Val rT := by
  have hc (k : ℕ) : Exp.lcb k coin.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb coin.lc) (Nat.zero_le k)
  have hf (k : ℕ) : Exp.lcb k (Occil.expMinusFactory : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (by is_lc)) (Nat.zero_le k)
  have hr (k : ℕ) : Exp.lcb k (Occil.rationalCoin : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (by is_lc)) (Nat.zero_le k)
  refine ⟨.lam (body coin), .lam ?_, ?_⟩ <;> apply Exp.lcb_imp_lc <;>
    simp [body, Exp.lcb, hc, hf, hr]

theorem opened {rT : Type} (coin : Val rT) (divisor : ℕ) :
    Exp.open' (body coin) (.lit (.int (divisor : ℤ))) =
      pl(&Occil.expMinusFactory &(PSRNDecayCoins.callback coin divisor).fst #()) := by
  have hf (k : ℕ) (v : Exp rT) :
      Exp.openRec k v Occil.expMinusFactory = Occil.expMinusFactory :=
    (Exp.open_lc k v _ (by is_lc)).symm
  have hr (k : ℕ) (v : Exp rT) :
      Exp.openRec k v Occil.rationalCoin = Occil.rationalCoin :=
    (Exp.open_lc k v _ (by is_lc)).symm
  simp [body, PSRNDecayCoins.callback, Exp.open', Exp.openRec, hf, hr,
    ProbLang.openRec_val_fst]

theorem bias_value (p : unitInterval) (divisor : ℕ) (hd : 0 < divisor) :
    (ExpMinusFactory.bias (p * PSRNDecayCoins.thinning divisor hd) : ℝ) =
      Real.exp (-(p : ℝ) / divisor) := by
  simp [ExpMinusFactory.bias, ExponentialFactory.decay, PSRNDecayCoins.thinning,
    RationalCoin.bias, div_eq_mul_inv]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

private theorem beta (E : CoPset) (coin : Val ℝ) (divisor : ℕ) (Φ : Val ℝ → IProp GF) :
    tglWp E pl(&Occil.expMinusFactory &(PSRNDecayCoins.callback coin divisor).fst #()) Φ ⊢
      tglWp E pl(&(value coin).fst #int (divisor : ℤ)) Φ := by
  rw [← opened]
  exact twp_beta E [] (body coin) (.int divisor) (value coin).lc Φ

variable [ProbLangDist.IsUniformInt ℝ] [ProbLangDist.IsUniformReal ℝ]

/-- Thinning and the exponential factory supply exp(-p/divisor), including p=0 and p=1. -/
theorem distSpec (E : CoPset) (p : unitInterval) (coin : Val ℝ)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (divisor : ℕ) (hd : 0 < divisor) :
    IsDistSpec (GF := GF) E pl(&(value coin).fst #int (divisor : ℤ))
      (RealCoin.law (ExpMinusFactory.bias (p * PSRNDecayCoins.thinning divisor hd))) Val.bool where
  spec F hF := by
    iintro Hcredit
    iapply beta E coin divisor _
    iapply (ExpMinusFactory.expMinusFactory_distSpec E _ _
      (PSRNDecayCoins.distSpec E p coin hcoin divisor hd)).spec F hF $$ Hcredit

end specification

end

end SampLib.PSRNUnknownRateDecay
