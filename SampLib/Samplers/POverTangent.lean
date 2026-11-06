import SampLib.Samplers.Division
import SampLib.Samplers.SineFactory
import SampLib.Samplers.CosineFactory
import Samplers.Bernoulli.Trigonometric

/-! # The tangent quotient factory

The numerator is the product of the input coin and its cosine factory. Racing it
against the sine-minus-numerator coin cancels the common sine denominator.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.POverTangent

noncomputable section

abbrev numeratorBias (p : unitInterval) : unitInterval :=
  p * FactorialSeriesFactory.bias .cos p

/-- The lower gap supplied to division is exactly `sin(p) - p cos(p)`. -/
theorem gap (p : unitInterval) :
    (SineFactory.bias p : ℝ) - numeratorBias p = Real.sin p - p * Real.cos p := by
  rw [SineFactory.bias_coe]
  simp only [numeratorBias, Set.Icc.coe_mul, FactorialSeriesFactory.bias_coe,
    FactorialSeries.value]

def bias (p : unitInterval) (e f : ℤ) (he : 0 < e) (hef : e < f)
    (h : (e : ℝ) / f ≤ Real.sin p - p * Real.cos p) : unitInterval :=
  Division.bias (SineFactory.bias p) (numeratorBias p) e f he hef (by rwa [gap])

theorem bias_coe (p : unitInterval) (e f : ℤ) (he : 0 < e) (hef : e < f)
    (h : (e : ℝ) / f ≤ Real.sin p - p * Real.cos p) :
    (bias p e f he hef h : ℝ) = p / Real.tan p := by
  rw [bias, Division.bias_coe, SineFactory.bias_coe]
  simp only [numeratorBias, Set.Icc.coe_mul, FactorialSeriesFactory.bias_coe,
    FactorialSeries.value]
  rw [Real.tan_eq_sin_div_cos, div_div_eq_mul_div]

private theorem sine_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.sineFactory = Occil.sineFactory :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem sine_fv {rT : Type} : (Occil.sineFactory : Exp rT).fv = ∅ := by
  simp [Occil.sineFactory, Exp.fv, FactorialSeriesFactory.factorialSeriesFactory_fv]

private theorem sine_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.sineFactory : Exp rT) = Occil.sineFactory :=
  Exp.closeRec_fresh x _ k (by simp [sine_fv])

private def numerator {rT : Type} (coin : Val rT) : Val rT :=
  ⟨.lam pl(if &coin.fst #() then &Occil.cosineFactory &coin.fst #() else #false),
    .lam (by is_lc), by is_lc⟩

private def denominator {rT : Type} (coin : Val rT) : Val rT :=
  ⟨.lam pl(&Occil.sineFactory &coin.fst #()), .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem numerator_spec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&(numerator coin).fst #())
      (RealCoin.law (numeratorBias p)) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    twp_bind pl(&coin.fst #())
    isimp only [numeratorBias, ← CoinProduct.expectation_preservation p
      (FactorialSeriesFactory.bias .cos p) F] at Hcredit
    iapply (hcoin.wp (CoinProduct.firstCredit (FactorialSeriesFactory.bias .cos p) F)
      (measurable_of_countable _) _) $$ Hcredit
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
      isimp only [CoinProduct.firstCredit, ite_true] at Hcredit
      simp only [CosineFactory.cosineFactory_openRec]
      iapply (CosineFactory.cosineFactory_distSpec E p coin hcoin).spec F hF $$ Hcredit

private theorem denominator_spec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&(denominator coin).fst #())
      (RealCoin.law (SineFactory.bias p)) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    simp only [sine_openRec]
    iapply (SineFactory.sineFactory_distSpec E p coin hcoin).spec F hF $$ Hcredit

/-- The full source domain is the supplied positive rational lower bound on the gap. -/
theorem pOverTangent_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (e f : ℤ) (he : 0 < e) (hef : e < f)
    (h : (e : ℝ) / f ≤ Real.sin p - p * Real.cos p) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.pOverTangent &coin.fst #int e #int f #())
      (RealCoin.law (bias p e f he hef h)) Val.bool where
  spec F hF := by
    iintro Hcredit
    iterate 5 twp_pure
    simp only [Division.division_openRec, Division.division_closeRec]
    isimp only [bias] at Hcredit
    simp only [CosineFactory.cosineFactory_closeRec, CosineFactory.cosineFactory_openRec,
      sine_closeRec, sine_openRec]
    have hd := (Division.division_distSpec E (SineFactory.bias p) (numeratorBias p)
      e f he hef (by rwa [gap]) (denominator coin) (numerator coin)
      (denominator_spec E p coin hcoin) (numerator_spec E p coin hcoin)).spec F hF
    simp only [numerator, denominator] at hd
    iapply hd $$ Hcredit

end specification

end

end SampLib.POverTangent
