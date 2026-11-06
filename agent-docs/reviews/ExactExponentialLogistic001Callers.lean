import SampLib.PSRN.Support.PSRNExponentialLogistic

open ProbLang
open scoped ENNReal

namespace ReviewExponentialLogistic001

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private def endpoint (b : Bool) : unitInterval := if b then 1 else 0
private def constantDecay (b : Bool) : Val rT :=
  ⟨.lam (.lit (.bool b)), .lam (by is_lc), by is_lc⟩

private theorem constant_spec (E : CoPset) (b : Bool) (arg : ℤ) :
    IsDistSpec (GF := GF) E pl(&(constantDecay b : Val rT).fst #int arg)
      (RealCoin.law (endpoint b)) Val.bool where
  spec F _ := by
    iintro Hcredit
    have hz : ((0 : unitInterval) : ℝ) = 0 := rfl
    have ho : ((1 : unitInterval) : ℝ) = 1 := rfl
    cases b <;> isimp only [endpoint, Bool.false_eq_true, ite_false, ite_true,
      RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf, hz, ho,
      ENNReal.ofReal_zero, ENNReal.ofReal_one, sub_self, sub_zero,
      zero_mul, one_mul, add_zero, zero_add] at Hcredit
    all_goals
      unfold constantDecay
      twp_pures
      twp_value
      imodintro
      iexists _
      iframe Hcredit
      itrivial

section digit

variable [ProbLangDist.IsUniformInt rT]

theorem framed (E : CoPset) (q : unitInterval) (decay : Val rT) (seen denominator : ℤ)
    (hdecay : IsDistSpec (GF := GF) E pl(&decay.fst #int (denominator * 2))
      (RealCoin.law q) Val.bool) (F : Bool → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (RealCoin.credit (ExponentialLogistic.bias q) F) ∗ R -∗
      tglWp E pl(&(ExponentialLogistic.Program.digitVal decay).fst #int seen #int denominator)
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  isimp only [← RealCoin.lintegral_law] at Hcredit
  iapply (ExponentialLogistic.digit_distSpec E q decay seen denominator hdecay).wp
    F (measurable_of_countable _) _ $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HR
  itrivial

example (E : CoPset) (b : Bool) (F : Bool → ℝ≥0∞) (R : IProp GF) :=
  framed E (endpoint b) (constantDecay b) (-37) 8
    (constant_spec E b 16) F R

example (E : CoPset) (R : IProp GF) :=
  framed E (endpoint false) (constantDecay false) 0 (-5)
    (constant_spec E false (-10)) (fun b => if b then ∞ else 0) R

example (E : CoPset) (R : IProp GF) :=
  framed E (endpoint true) (constantDecay true) (-1) 0
    (constant_spec E true 0) (fun _ => ∞) R

end digit

example : RealCoin.credit (ExponentialLogistic.bias 0) (fun b => if b then ∞ else 0) = 0 := by
  have hzero : ExponentialLogistic.bias 0 = 0 := by
    apply Subtype.ext
    norm_num [ExponentialLogistic.bias_coe]
  simp [hzero, RealCoin.credit, RealCoin.pmf]

example : (ExponentialLogistic.bias 1 : ℝ) = 1 / 2 := by
  norm_num [ExponentialLogistic.bias_coe]

#print axioms SampLib.ExponentialLogistic.Program.source_eq
#print axioms SampLib.ExponentialLogistic.twp_loop
#print axioms SampLib.ExponentialLogistic.digit_distSpec
#print axioms constant_spec
#print axioms framed

end
end ReviewExponentialLogistic001
