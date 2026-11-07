import SampLib.PSRN.PSRNPowerCoin
import SampLib.Uniform.RationalCoin
import SampLib.Core.BetaStep

/-! # The log-rate exponential's actual rational-power decay callback -/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNLogRateDecay

noncomputable section

def rate (x y : ℤ) : ℝ := Real.log ((x : ℝ) / y)

theorem rate_pos {x y : ℤ} (hy : 0 < y) (hxy : y < x) : 0 < rate x y := by
  apply Real.log_pos
  exact (one_lt_div (by exact_mod_cast hy : (0 : ℝ) < y)).mpr (by exact_mod_cast hxy)

def base (x y : ℤ) (hy : 0 < y) (hxy : y < x) : unitInterval :=
  RationalCoin.bias y x hy.le (by omega) hxy.le

def coin {rT : Type} (x y : ℤ) : Val rT :=
  ⟨.lam pl(&Occil.rationalCoin #y #x), .lam (by is_lc), by is_lc⟩

def body {rT : Type} (x y : ℤ) : Exp rT :=
  .app (.app (.app (.app Occil.PSRN.powerCoin (coin x y).fst) (.lit (.int 1))) (.bvar 0))
    (.lit .unit)

/-- The divisor is the argument of the original source's decay closure. -/
def value {rT : Type} (x y : ℤ) : Val rT := by
  have hp (k : ℕ) : Exp.lcb k (Occil.PSRN.powerCoin : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (by is_lc)) (Nat.zero_le k)
  have hc (k : ℕ) : Exp.lcb k (coin (rT := rT) x y).fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (coin (rT := rT) x y).lc) (Nat.zero_le k)
  refine ⟨.lam (body x y), .lam ?_, ?_⟩ <;> apply Exp.lcb_imp_lc <;>
    simp [body, Exp.lcb, hp, hc]

theorem opened {rT : Type} (x y : ℤ) (divisor : ℕ) :
    Exp.open' (body (rT := rT) x y) (.lit (.int (divisor : ℤ))) =
      pl(&Occil.PSRN.powerCoin &(coin x y).fst #1 #int (divisor : ℤ) #()) := by
  have hp (k : ℕ) (v : Exp rT) :
      Exp.openRec k v Occil.PSRN.powerCoin = Occil.PSRN.powerCoin :=
    (Exp.open_lc k v _ (by is_lc)).symm
  simp [body, Exp.open', Exp.openRec, hp, ProbLang.openRec_val_fst]

/-- The power trial is precisely exp(-log(x/y)/divisor). -/
theorem bias_value (x y : ℤ) (hy : 0 < y) (hxy : y < x)
    (divisor : ℕ) (hd : 0 < divisor) :
    (RationalPower.bias (base x y hy hxy) 1 divisor hd : ℝ) =
      Real.exp (-rate x y / divisor) := by
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have hx' : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  simp only [RationalPower.bias, base, RationalCoin.bias, Nat.cast_one]
  change ((y : ℝ) / x) ^ ((1 : ℝ) / divisor) = _
  rw [Real.rpow_def_of_pos (div_pos hy' hx'), rate,
    Real.log_div hy'.ne' hx'.ne', Real.log_div hx'.ne' hy'.ne']
  congr 1
  ring

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem beta (E : CoPset) (x y : ℤ) (divisor : ℕ) (Φ : Val rT → IProp GF) :
    tglWp E pl(&Occil.PSRN.powerCoin &(coin x y).fst #1 #int (divisor : ℤ) #()) Φ ⊢
      tglWp E pl(&(value x y).fst #int (divisor : ℤ)) Φ := by
  rw [← opened]
  exact twp_beta E [] (body x y) (.int divisor) (value x y).lc Φ

variable [ProbLangDist.IsUniformInt rT]

private theorem coin_spec (E : CoPset) (x y : ℤ) (hy : 0 < y) (hxy : y < x) :
    IsDistSpec (GF := GF) E pl(&(coin x y).fst #()) (RealCoin.law (base x y hy hxy)) Val.bool where
  spec F hF := by
    have hbase : IsDistSpec (GF := GF) E pl(&Occil.rationalCoin #y #x)
        (RealCoin.law (base x y hy hxy)) Val.bool :=
      RationalCoin.rationalCoin_distSpec E y x hy.le (by omega) hxy.le
    iintro Hcredit
    twp_pure
    simp only [RationalCoin.rationalCoin_openRec]
    iapply hbase.spec F hF $$ Hcredit

/-- Each use independently realizes the required rational-power decay probability. -/
theorem distSpec (E : CoPset) (x y : ℤ) (hy : 0 < y) (hxy : y < x)
    (divisor : ℕ) (hd : 0 < divisor) :
    IsDistSpec (GF := GF) E pl(&(value x y).fst #int (divisor : ℤ))
      (RealCoin.law (RationalPower.bias (base x y hy hxy) 1 divisor hd)) Val.bool where
  spec F hF := by
    iintro Hcredit
    iapply beta E x y divisor _
    iapply (PSRNPowerCoin.powerCoin_distSpec E _ 1 divisor hd (coin x y)
      (coin_spec E x y hy hxy)).spec F hF $$ Hcredit

end specification

end

end SampLib.PSRNLogRateDecay
