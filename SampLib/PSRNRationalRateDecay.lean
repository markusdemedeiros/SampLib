import SampLib.Samplers.ExpMinusRational
import SampLib.BetaStep

/-! # The rational-rate exponential's exact integer decay callback -/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNRationalRateDecay

noncomputable section

theorem rate_pos (a b : ℤ) (ha : 0 < a) (hb : 0 < b) : 0 < (a : ℝ) / b :=
  div_pos (by exact_mod_cast ha) (by exact_mod_cast hb)

def body {rT : Type} (a b : ℤ) : Exp rT :=
  .app (.app (.app Occil.expMinusRational (.lit (.int a)))
    (.binop .mult (.lit (.int b)) (.bvar 0))) (.lit .unit)

def value {rT : Type} (a b : ℤ) : Val rT := by
  have he (k : ℕ) : Exp.lcb k (Occil.expMinusRational : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb ExpMinusRational.expMinusRational_lc) (Nat.zero_le k)
  refine ⟨.lam (body a b), .lam ?_, ?_⟩ <;> apply Exp.lcb_imp_lc <;>
    simp [body, Exp.lcb, he]

theorem opened {rT : Type} (a b : ℤ) (d : ℕ) :
    Exp.open' (body (rT := rT) a b) (.lit (.int (d : ℤ))) =
      pl(&Occil.expMinusRational #a (#b * #int (d : ℤ)) #()) := by
  simp [body, Exp.open', Exp.openRec, ExpMinusRational.expMinusRational_openRec]

theorem bias_value (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (d : ℕ) (hd : 0 < d) :
    (ExpMinusRational.bias a (b * d) ha (mul_pos hb (by exact_mod_cast hd)) : ℝ) =
      Real.exp (-((a : ℝ) / b) / d) := by
  simp [ExpMinusRational.bias, Int.cast_mul, Int.cast_natCast, div_div, neg_div]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem beta (E : CoPset) (a b : ℤ) (d : ℕ) (Φ : Val rT → IProp GF) :
    tglWp E pl(&Occil.expMinusRational #a (#b * #int (d : ℤ)) #()) Φ ⊢
      tglWp E pl(&(value a b).fst #int (d : ℤ)) Φ := by
  rw [← opened]
  exact twp_beta E [] (body a b) (.int d) (value a b).lc Φ

variable [ProbLangDist.IsUniformInt rT]

/-- Each divisor gives an exact rational negative-exponential coin. -/
theorem distSpec (E : CoPset) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b)
    (d : ℕ) (hd : 0 < d) :
    IsDistSpec (GF := GF) E pl(&(value a b).fst #int (d : ℤ))
      (RealCoin.law (ExpMinusRational.bias a (b * d) ha
        (mul_pos hb (by exact_mod_cast hd)))) Val.bool where
  spec F hF := by
    iintro Hcredit
    iapply beta E a b d _
    twp_pure
    simp only [Exp.ofVal]
    iapply (ExpMinusRational.expMinusRational_distSpec E a (b * d) ha
      (mul_pos hb (by exact_mod_cast hd))).spec F hF $$ Hcredit

end specification

end

end SampLib.PSRNRationalRateDecay
