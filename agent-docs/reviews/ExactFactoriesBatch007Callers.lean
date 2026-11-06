import SampLib.Constants.TanhHalf
import SampLib.Bernoulli.ExpDivThree
import SampLib.Bernoulli.BinaryExponentialRational

open ProbLang
open scoped ENNReal

namespace ExactFactoriesReview007

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

example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (TanhHalf.tanhHalf_distSpec E) F I

example (E : CoPset) (I : IProp GF) :=
  frame (TanhHalf.tanhHalf_distSpec E) (fun b => if b then ∞ else 0) I

example : (EulerHyperbolic.bias : ℝ) = Real.tanh (1 / 2) := EulerHyperbolic.bias_coe

example : FromBounds.encodeInterval (rT := rT) (EulerHyperbolic.interval 0) =
    Val.pair (Val.int 4) (Val.pair (Val.int 6) (Val.int 12)) := rfl

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ExpDivThree.expDivThree_distSpec E p coin hcoin) F I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool)
    (I : IProp GF) :=
  frame (ExpDivThree.expDivThree_distSpec E 0 coin hcoin) (fun b => if b then ∞ else 0) I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 1) Val.bool)
    (I : IProp GF) :=
  frame (ExpDivThree.expDivThree_distSpec E 1 coin hcoin) (fun b => if b then 0 else ∞) I

example : (ExpDivThree.bias 0 : ℝ) = 1 / 3 := by
  rw [ExpDivThree.bias_coe]
  norm_num

example : (ExpDivThree.bias 1 : ℝ) = Real.exp 1 / 3 := ExpDivThree.bias_coe 1

example (E : CoPset) (p : unitInterval) (a b : ℕ) (hb : 0 < b) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (BinaryExponentialRational.binaryExponentialRational_distSpec E p a b hb coin hcoin) F I

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (I : IProp GF) :=
  frame (BinaryExponentialRational.binaryExponentialRational_distSpec E p 0 7
    (by norm_num) coin hcoin) (fun b => if b then 0 else ∞) I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool)
    (I : IProp GF) :=
  frame (BinaryExponentialRational.binaryExponentialRational_distSpec E 0 8 3
    (by norm_num) coin hcoin) (fun b => if b then 0 else ∞) I

example (p : unitInterval) : (BinaryExponentialRational.bias p 0 7 : ℝ) = 1 := by
  simp [BinaryExponentialRational.bias_coe]

example (a b : ℕ) : (BinaryExponentialRational.bias 0 a b : ℝ) = 1 := by
  simp [BinaryExponentialRational.bias_coe]

#print axioms TanhHalf.tanhHalf_distSpec
#print axioms EulerHyperbolic.bias_coe
#print axioms ExpDivThree.expDivThree_distSpec
#print axioms ExpDivThree.expectation
#print axioms BinaryExponentialRational.binaryExponentialRational_distSpec
#print axioms BinaryExponentialRational.bias_coe

end

end ExactFactoriesReview007
