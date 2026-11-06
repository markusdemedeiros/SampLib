import SampLib.Bernoulli.Support.LinearFactorySyntax
import SampLib.Bernoulli.CoinMean

/-! # Addition by a linear factory

The mean coin has bias `(p+q)/2`; the verified expanding factory doubles it.
This is a derived construction with the supplied positive margin.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.Addition

noncomputable section

private theorem mean_ratio (p q : unitInterval) :
    Gambler.ratio (CoinMean.bias p q) 2 1 = (p : ℝ) + q := by
  simp only [Gambler.ratio, CoinMean.bias, CoinConditional.bias, Set.Icc.coe_convexComb]
  norm_num [VonNeumann.fairBias]
  ring

private theorem admissible (p q : unitInterval) (e f : ℤ) (he : 0 < e) (hef : e < f)
    (h : (p : ℝ) + q ≤ 1 - (e : ℝ) / f) :
    LinearFactory.Admissible (CoinMean.bias p q) 2 1 e f := by
  refine ⟨by norm_num, by norm_num, fun _ => ⟨he, hef, ?_⟩⟩
  simpa only [mean_ratio] using h

/-- The sum bias, normalized by the supplied strict upper margin. -/
def bias (p q : unitInterval) (e f : ℤ) (he : 0 < e) (hef : e < f)
    (h : (p : ℝ) + q ≤ 1 - (e : ℝ) / f) : unitInterval :=
  LinearFactory.bias (CoinMean.bias p q) 2 1 e f (admissible p q e f he hef h)

theorem bias_coe (p q : unitInterval) (e f : ℤ) (he : 0 < e) (hef : e < f)
    (h : (p : ℝ) + q ≤ 1 - (e : ℝ) / f) : (bias p q e f he hef h : ℝ) = (p : ℝ) + q := by
  exact mean_ratio p q

private def source {rT : Type _} : Val rT :=
  ⟨Occil.FactoryExtra.addition, .lam (by is_lc), by is_lc⟩

private theorem source_fst {rT : Type _} :
    (source (rT := rT)).fst = Occil.FactoryExtra.addition := rfl

private def callback {rT : Type _} (left right : Val rT) : Val rT :=
  ⟨.lam pl(&Occil.coinMean &left.fst &right.fst #()), .lam (by is_lc), by is_lc⟩

private theorem coinMean_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.coinMean = Occil.coinMean :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem coinMean_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.coinMean : Exp rT) = Occil.coinMean :=
  Exp.closeRec_fresh x _ k (by simp [Occil.coinMean, Exp.fv, FairCoin.fairCoin_fv])

theorem addition_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.FactoryExtra.addition = Occil.FactoryExtra.addition :=
  (Exp.open_lc k e _ (by is_lc)).symm

theorem addition_fv {rT : Type} : (Occil.FactoryExtra.addition : Exp rT).fv = ∅ := by
  have hmean : (Occil.coinMean : Exp rT).fv = ∅ := by
    simp [Occil.coinMean, Exp.fv, FairCoin.fairCoin_fv]
  simp [Occil.FactoryExtra.addition, Exp.fv, coinMean_closeRec, hmean,
    LinearFactorySyntax.linear_closeRec, LinearFactorySyntax.linear_fv]

theorem addition_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.FactoryExtra.addition : Exp rT) = Occil.FactoryExtra.addition :=
  Exp.closeRec_fresh x _ k (by simp [addition_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable [ProbLangDist.IsUniformInt rT]
local bi (IProp GF)

private theorem callback_spec (E : CoPset) (p q : unitInterval) (left right : Val rT)
    (hleft : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hright : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool) :
    IsDistSpec (GF := GF) E pl(&(callback left right).fst #()) (CoinMean.law p q) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_step
    simp [Exp.open', Exp.openRec, ProbLang.openRec_val_fst, coinMean_openRec]
    iapply (CoinMean.coinMean_distSpec E p q left right hleft hright).spec F hF $$ Hcredit

/-- Derived sum law for every valid positive rational margin. -/
theorem addition_distSpec (E : CoPset) (p q : unitInterval) (e f : ℤ)
    (he : 0 < e) (hef : e < f) (h : (p : ℝ) + q ≤ 1 - (e : ℝ) / f)
    (left right : Val rT)
    (hleft : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hright : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.addition &left.fst &right.fst #int e #int f #())
      (RealCoin.law (bias p q e f he hef h)) Val.bool where
  spec F hF := by
    have hl := LinearFactory.linear_distSpec (rT := rT) (GF := GF) E (CoinMean.bias p q)
      2 1 e f (admissible p q e f he hef h) (callback left right)
      (callback_spec E p q left right hleft hright)
    simp only [callback] at hl
    iintro Hcredit
    rw [← source_fst (rT := rT)]
    iterate 5 (twp_step; simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Exp.ofVal,
      Var.internal.injEq, ProbLang.openRec_val_fst, coinMean_openRec, coinMean_closeRec,
      LinearFactorySyntax.linear_openRec, LinearFactorySyntax.linear_closeRec])
    isimp only [bias] at Hcredit
    iapply hl.spec F hF $$ Hcredit

end specification

end

end SampLib.Addition
