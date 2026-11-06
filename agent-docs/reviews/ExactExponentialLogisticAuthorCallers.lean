import SampLib.PSRN.Support.PSRNExponentialLogistic
import SampLib.Bernoulli.Support.CoinExpression

open ProbLang
open scoped ENNReal

namespace ExponentialLogisticAuthor

open SampLib SampLib.ExponentialLogistic
open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

noncomputable section

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (q : unitInterval) (decay : Val rT) (seen denominator : ℤ)
    (hdecay : IsDistSpec (GF := GF) E pl(&decay.fst #int (denominator * 2))
      (RealCoin.law q) Val.bool) (F : Bool → ℝ≥0∞) (R : IProp GF) :
    iprop(↯ (RealCoin.credit (bias q) F) ∗ R) ⊢
      tglWp E pl(&(Program.digitVal decay).fst #int seen #int denominator)
        (fun v => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  isimp only [← RealCoin.lintegral_law] at Hcredit
  iapply ((digit_distSpec E q decay seen denominator hdecay).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HR
  itrivial

private def zeroDecay : Val rT := ⟨pl(fun divisor, #false), .lam (by is_lc), by is_lc⟩
private def oneDecay : Val rT := ⟨pl(fun divisor, #true), .lam (by is_lc), by is_lc⟩

omit [ProbLangDist.IsUniformInt rT] in
private theorem zeroDecay_spec (E : CoPset) (denominator : ℤ) :
    IsDistSpec (GF := GF) E pl(&zeroDecay.fst #int (denominator * 2))
      (RealCoin.law 0) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    iapply (CoinExpression.false_spec (rT := rT) (GF := GF) E).spec F hF $$ Hcredit

omit [ProbLangDist.IsUniformInt rT] in
private theorem oneDecay_spec (E : CoPset) (denominator : ℤ) :
    IsDistSpec (GF := GF) E pl(&oneDecay.fst #int (denominator * 2))
      (RealCoin.law 1) Val.bool where
  spec F _ := by
    iintro Hcredit
    isimp only [RealCoin.lintegral_law, RealCoin.credit_one] at Hcredit
    twp_pure
    twp_value
    imodintro
    iexists true
    iframe Hcredit
    itrivial

example (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&(Program.digitVal (zeroDecay (rT := rT))).fst #97 #3)
      (RealCoin.law (bias 0)) Val.bool :=
  digit_distSpec E 0 zeroDecay 97 3 (zeroDecay_spec E 3)

example (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&(Program.digitVal (oneDecay (rT := rT))).fst #(-5) #11)
      (RealCoin.law (bias 1)) Val.bool :=
  digit_distSpec E 1 oneDecay (-5) 11 (oneDecay_spec E 11)

example : (bias 0 : ℝ) = 0 := by rw [bias_coe]; norm_num
example : (bias 1 : ℝ) = 1 / 2 := by rw [bias_coe]; norm_num
example : RealCoin.credit (bias 0) (fun b => if b then ⊤ else 0) = 0 := by
  simp [RealCoin.credit, RealCoin.pmf, bias_coe]
example (q : unitInterval) : RealCoin.credit (bias q) (fun _ => ⊤) = (⊤ : ℝ≥0∞) := by
  rw [← RealCoin.lintegral_law]
  simp only [MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one]

#print axioms SampLib.ExponentialLogistic.Program.source_eq
#print axioms SampLib.ExponentialLogistic.bias_coe
#print axioms SampLib.ExponentialLogistic.twp_loop
#print axioms SampLib.ExponentialLogistic.digit_distSpec

end
end ExponentialLogisticAuthor
