import SampLib.Samplers.ArctanFactory
import SampLib.Samplers.ArctanOverPi

open ProbLang
open scoped ENNReal

namespace ExactFactoriesReview006

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
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

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ArctanOverPFactory.arctanOverPFactory_distSpec E p coin hcoin) F I

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ArctanFactory.arctanFactory_distSpec E p coin hcoin) F I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool)
    (I : IProp GF) :=
  frame (ArctanOverPFactory.arctanOverPFactory_distSpec E 0 coin hcoin)
    (fun b => if b then 0 else ∞) I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool)
    (I : IProp GF) :=
  frame (ArctanFactory.arctanFactory_distSpec E 0 coin hcoin)
    (fun b => if b then ∞ else 0) I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 1) Val.bool)
    (I : IProp GF) :=
  frame (ArctanOverPFactory.arctanOverPFactory_distSpec E 1 coin hcoin)
    (fun b => if b then ∞ else 0) I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 1) Val.bool)
    (I : IProp GF) :=
  frame (ArctanFactory.arctanFactory_distSpec E 1 coin hcoin)
    (fun b => if b then 0 else ∞) I

example : (ArctanOverPFactory.bias 0 : ℝ) = 1 := ArctanFactory.ratio_coe_zero

example : (ArctanOverPFactory.bias 1 : ℝ) = Real.pi / 4 := by
  rw [ArctanFactory.ratio_coe_of_ne_zero 1 (by norm_num)]
  simp [Real.arctan_one]

example : (ArctanFactory.bias 0 : ℝ) = 0 := by simp

example : (ArctanFactory.bias 1 : ℝ) = Real.pi / 4 := by simp [Real.arctan_one]

example : RealCoin.credit (ArctanOverPFactory.bias 0) (fun b => if b then 0 else ∞) = 0 := by
  have h : ArctanOverPFactory.bias 0 = 1 := Subtype.ext ArctanFactory.ratio_coe_zero
  simp [h, RealCoin.credit, RealCoin.pmf]

example : RealCoin.credit (ArctanFactory.bias 0) (fun b => if b then ∞ else 0) = 0 := by
  have h : ArctanFactory.bias 0 = 0 := Subtype.ext (by simp)
  simp [h, RealCoin.credit, RealCoin.pmf]

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ArctanOverPi.arctanOverPi_distSpec E p coin hcoin) F I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool)
    (I : IProp GF) :=
  frame (ArctanOverPi.arctanOverPi_distSpec E 0 coin hcoin)
    (fun b => if b then ∞ else 0) I

example : (ArctanOverPi.bias 0 : ℝ) = 0 := by simp

example : (ArctanOverPi.bias 1 : ℝ) = 1 / 4 := by
  rw [ArctanOverPi.bias_coe]
  simp only [Set.Icc.coe_one, Real.arctan_one]
  field_simp

#print axioms ArctanOverPi.arctanOverPi_distSpec
#print axioms ArctanOverPFactory.arctanOverPFactory_distSpec
#print axioms ArctanFactory.arctanFactory_distSpec
#print axioms ArctanOverPFactory.expectation
#print axioms ArctanFactory.integral
#print axioms ArctanFactory.success_mass

end

end ExactFactoriesReview006
