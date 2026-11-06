import SampLib.Samplers.ArctanOverPFactory

/-! # The arctangent factory

One outer input flip multiplies the continuous atan(p)/p ratio by p.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.ArctanFactory

noncomputable section

def bias (p : unitInterval) : unitInterval := p * ratio p

@[simp] theorem bias_coe (p : unitInterval) : (bias p : ℝ) = Real.arctan p := by
  change (p : ℝ) * (ratio p : ℝ) = Real.arctan p
  by_cases hp : (p : ℝ) = 0
  · simp [hp]
  · rw [ratio_coe_of_ne_zero p hp]
    field_simp

theorem arctanFactory_fv {rT : Type} : (Occil.arctanFactory : Exp rT).fv = ∅ := by
  simp [Occil.arctanFactory, Exp.fv, ArctanOverPFactory.arctanOverPFactory_fv]

@[simp] theorem arctanFactory_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.arctanFactory = Occil.arctanFactory :=
  (Exp.open_lc k e _ (by is_lc)).symm

@[simp] theorem arctanFactory_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.arctanFactory : Exp rT) = Occil.arctanFactory :=
  Exp.closeRec_fresh x _ k (by simp [arctanFactory_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The outer product restores atan(p), including the deterministic p=0 endpoint. -/
theorem arctanFactory_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.arctanFactory &coin.fst #())
      (RealCoin.law (bias p)) Val.bool where
  spec F hF := by
    iintro Hcredit
    iterate 2 twp_pure
    twp_bind pl(&coin.fst #())
    isimp only [bias, ← CoinProduct.expectation_preservation p (ratio p) F] at Hcredit
    iapply (hcoin.wp (CoinProduct.firstCredit (ratio p) F) (measurable_of_countable _) _)
      $$ Hcredit
    iintro %b Hcredit
    cases b
    · twp_pures
      twp_value
      imodintro
      iexists false
      isimp only [CoinProduct.firstCredit, Bool.false_eq_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pure
      simp only [ArctanOverPFactory.arctanOverPFactory_openRec,
        ArctanOverPFactory.arctanOverPFactory_closeRec]
      isimp only [CoinProduct.firstCredit, ite_true] at Hcredit
      iapply (ArctanOverPFactory.arctanOverPFactory_distSpec E p coin hcoin).spec F hF
        $$ Hcredit

end specification

end

end SampLib.ArctanFactory
