import SampLib.Samplers.ExpMinusMartingale
import SampLib.Samplers.CosineFactory
import SampLib.Samplers.SineFactory
import SampLib.Samplers.EpsilonDivision
import SampLib.Distributions.FactorialSeriesMean
import SampLib.Templates
import Metrology.Iris.LocalBI
open ProbLang
open scoped ENNReal
namespace ExpansionFactoriesReview
noncomputable section
open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib
variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)
theorem frame {E : CoPset} {e : Exp rT} {μ : MeasureTheory.Measure Bool}
    [MeasureTheory.IsProbabilityMeasure μ]
    (h : IsDistSpec (GF := GF) E e μ Val.bool) (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂μ) ∗ I -∗ tglWp E e
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply (h.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial

example (E : CoPset) (coin : Val rT) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (EpsilonDivision.epsilonDivision_zero_distSpec (GF := GF)
    E 2 (-9) 3 (by norm_num) (by norm_num) (by norm_num) coin) F I
variable [ProbLangDist.IsUniformInt rT]
example (E : CoPset) (coin : Val rT) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (EpsilonDivision.epsilonDivision_fullLower_distSpec (GF := GF)
    E 1 2 3 (by norm_num) (by norm_num) (by norm_num) coin) F I
example (E : CoPset) (p : unitInterval) (a b l d : ℤ)
    (h : EpsilonDivision.Admissible p a b l d) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (EpsilonDivision.epsilonDivision_distSpec E p a b l d h coin hc) F I
private def half : unitInterval := ⟨1/2, by norm_num, by norm_num⟩
example : EpsilonDivision.Admissible half 1 4 1 2 := by
  norm_num [EpsilonDivision.Admissible, half]
example (h : EpsilonDivision.Admissible half 1 4 1 2) :
    (EpsilonDivision.bias half 1 4 1 2 h : ℝ) = 1/2 :=
  (EpsilonDivision.bias_coe _ _ _ _ _ h).trans (by norm_num [half])
example : EpsilonDivision.Admissible 0 0 2 (-9) 3 := by
  norm_num [EpsilonDivision.Admissible]
example (h : EpsilonDivision.Admissible 0 0 2 (-9) 3) :
    (∫⁻ b, (if b then ∞ else 0 : ℝ≥0∞)
      ∂RealCoin.law (EpsilonDivision.bias 0 0 2 (-9) 3 h)) = 0 := by
  rw [EpsilonDivision.bias_zero]
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]
private def factorialMean (m : FactorialSeries.Mode) (p : unitInterval) : ℝ :=
  GeometricThreshold.mean (FactorialSeries.callbackBias m p)
    (FactorialSeries.partialBias m) (FactorialSeries.limitBias m) 0
example (m : FactorialSeries.Mode) :
    (factorialMean m 0 : ℝ) = 1 := by
  rw [factorialMean, FactorialSeries.mean_eq_value]
  cases m <;> norm_num [FactorialSeries.value, Real.sinc]
example : (factorialMean .exp 1 : ℝ) = Real.exp (-1) := by
  simpa only [factorialMean, FactorialSeries.value, Set.Icc.coe_one] using
    FactorialSeries.mean_eq_value .exp 1
example : (factorialMean .cos 1 : ℝ) = Real.cos 1 := by
  simpa only [factorialMean, FactorialSeries.value, Set.Icc.coe_one] using
    FactorialSeries.mean_eq_value .cos 1
example : (factorialMean .sinc 1 : ℝ) = Real.sinc 1 := by
  simpa only [factorialMean, FactorialSeries.value, Set.Icc.coe_one] using
    FactorialSeries.mean_eq_value .sinc 1
example (E : CoPset) (p : unitInterval) (m : FactorialSeries.Mode) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (FactorialSeriesFactory.factorialSeriesFactory_distSpec E p m coin hc) F I
example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ExpMinusMartingale.expMinusMartingale_distSpec E p coin hc) F I
example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (CosineFactory.cosineFactory_distSpec E p coin hc) F I
example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (SineFactory.sineFactory_distSpec E p coin hc) F I

private def constantCallback {rT : Type} (b : Bool) : Val rT :=
  ⟨.lam (.lit (.bool b)), .lam (by is_lc), by is_lc⟩
omit [ProbLangDist.IsUniformInt rT] in
private theorem constant_spec (E : CoPset) (b : Bool) :
    IsDistSpec (GF := GF) E pl(&(constantCallback (rT := rT) b).fst #())
      (RealCoin.law (if b then 1 else 0)) Val.bool where
  spec F _ := by
    iintro Hcredit
    twp_pure
    twp_value
    imodintro
    iexists b
    cases b
    · isimp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf] at Hcredit
      iframe Hcredit
      itrivial
    · isimp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf] at Hcredit
      iframe Hcredit
      itrivial
example (E : CoPset) (m : FactorialSeries.Mode) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (FactorialSeriesFactory.factorialSeriesFactory_distSpec E 0 m
    (constantCallback false) (constant_spec E false)) F I
example (E : CoPset) (m : FactorialSeries.Mode) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (FactorialSeriesFactory.factorialSeriesFactory_distSpec E 1 m
    (constantCallback true) (constant_spec E true)) F I
example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (SineFactory.sineFactory_distSpec E 0
    (constantCallback false) (constant_spec E false)) F I
example (m : FactorialSeries.Mode) : RealCoin.credit (FactorialSeriesFactory.bias m 0)
    (fun b => if b then 0 else ∞) = 0 := by
  have hb : FactorialSeriesFactory.bias m 0 = 1 := by
    apply Subtype.ext
    cases m <;> norm_num [FactorialSeriesFactory.bias, FactorialSeries.value, Real.sinc]
  rw [hb]
  simp [RealCoin.credit, RealCoin.pmf]
example : RealCoin.credit (SineFactory.bias 0) (fun b => if b then ∞ else 0) = 0 := by
  have hb : SineFactory.bias 0 = 0 := Subtype.ext (by simp)
  rw [hb]
  simp [RealCoin.credit, RealCoin.pmf]
example (m : FactorialSeries.Mode) (p : unitInterval) (F : Bool → ℝ≥0∞) :
    ∃ N, DyadicPosterior.credit [] (FactorialSeries.horizonCredit m p (N+1) 0 F) ≤
      RealCoin.credit (FactorialSeries.meanBias m p) F + ∞ :=
  FactorialSeries.exists_horizon m p F ∞ (by simp)

#print axioms SampLib.FactorialSeriesFactory.factorialSeriesFactory_distSpec
#print axioms SampLib.FactorialSeriesFactory.twp_factorialSeriesFactory
#print axioms SampLib.ExpMinusMartingale.expMinusMartingale_distSpec
#print axioms SampLib.CosineFactory.cosineFactory_distSpec
#print axioms SampLib.SineFactory.sineFactory_distSpec
#print axioms SampLib.SineFactory.bias_coe
#print axioms SampLib.FactorialSeries.expectation
#print axioms SampLib.FactorialSeries.initial_continuation
#print axioms SampLib.FactorialSeries.exists_horizon
#print axioms SampLib.FactorialSeries.unresolved_credit
#print axioms SampLib.GeometricThreshold.credit_step
#print axioms SampLib.GeometricThreshold.mixture_expectation

#print axioms SampLib.EpsilonDivision.epsilonDivision_distSpec
#print axioms SampLib.EpsilonDivision.epsilonDivision_zero_distSpec
#print axioms SampLib.EpsilonDivision.epsilonDivision_fullLower_distSpec
#print axioms SampLib.EpsilonDivision.expectation
#print axioms SampLib.FactorialSeries.mean_eq_value
#print axioms SampLib.FactorialSeries.value_mem
end
end ExpansionFactoriesReview
