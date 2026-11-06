import SampLib.Samplers.PSRNPowerCoin

open ProbLang
open scoped ENNReal

namespace ReviewExactStructured006

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private def endpoint (b : Bool) : unitInterval := if b then 1 else 0

private def constantCoin (b : Bool) : Val rT :=
  ⟨.lam (.lit (.bool b)), .lam (by is_lc), by is_lc⟩

private theorem constant_spec (E : CoPset) (b : Bool) :
    IsDistSpec (GF := GF) E pl(&(constantCoin b : Val rT).fst #())
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
      unfold constantCoin
      twp_pures
      twp_value
      imodintro
      iexists _
      iframe Hcredit
      itrivial

theorem frame {E : CoPset} {e : Exp rT} {p : unitInterval}
    (h : IsDistSpec (GF := GF) E e (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (RealCoin.credit p F) ∗ R -∗ tglWp E e
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  isimp only [← RealCoin.lintegral_law] at Hcredit
  iapply h.wp F (measurable_of_countable _) _ $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HR
  itrivial

section powers

variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) (p : unitInterval) (a b : ℕ) (hb : 0 < b) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (R : IProp GF) :=
  frame (PSRNPowerCoin.powerCoin_distSpec E p a b hb coin hcoin) F R

/-- Zero numerator with an always-false input exercises the convention0^0=1. -/
example (E : CoPset) (R : IProp GF) :=
  frame (PSRNPowerCoin.powerCoin_distSpec E (endpoint false) 0 7 (by decide)
    (constantCoin false) (constant_spec E false)) (fun b => if b then 0 else ∞) R

/-- Mixed whole and fractional powers at both input endpoints. -/
example (E : CoPset) (b : Bool) (F : Bool → ℝ≥0∞) (R : IProp GF) :=
  frame (PSRNPowerCoin.powerCoin_distSpec E (endpoint b) 5 3 (by decide)
    (constantCoin b) (constant_spec E b)) F R

example (E : CoPset) (R : IProp GF) :=
  frame (PSRNPowerCoin.powerCoin_distSpec E (endpoint true) 2 3 (by decide)
    (constantCoin true) (constant_spec E true)) (fun b => if b then 0 else ∞) R

example (E : CoPset) (R : IProp GF) :=
  frame (PSRNPowerCoin.powerCoin_distSpec E (endpoint false) 6 3 (by decide)
    (constantCoin false) (constant_spec E false)) (fun _ => ∞) R

end powers

example : RationalPower.bias 0 0 7 (by decide) = 1 := by
  apply Subtype.ext
  simp [RationalPower.bias]

example : RationalPower.bias 0 5 3 (by decide) = 0 := by
  apply Subtype.ext
  norm_num [RationalPower.bias]

example : RationalPower.bias 1 2 3 (by decide) = 1 := by
  apply Subtype.ext
  simp [RationalPower.bias]

#print axioms SampLib.PSRNPowerCoin.powerCoin_distSpec
#print axioms SampLib.PSRNPowerCoin.expectation
#print axioms SampLib.RationalPower.power_split
#print axioms frame

end
end ReviewExactStructured006
