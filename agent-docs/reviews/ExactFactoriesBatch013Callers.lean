import SampLib.Samplers.ExpMinusExp

open ProbLang
open scoped ENNReal

namespace ExactFactoriesReview013

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
    (m : ℕ) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ExpMinusExp.expMinusExp_distSpec E p coin hcoin m) F I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool)
    (I : IProp GF) :=
  frame (ExpMinusExp.expMinusExp_distSpec E 0 coin hcoin 0)
    (fun b => if b then ∞ else 0) I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 1) Val.bool)
    (I : IProp GF) :=
  frame (ExpMinusExp.expMinusExp_distSpec E 1 coin hcoin 0)
    (fun b => if b then 0 else ∞) I

example : (ExpMinusExp.bias 0 0 : ℝ) = Real.exp (-1) := by
  rw [ExpMinusExp.bias_coe]
  norm_num

example : (ExpMinusExp.bias 1 0 : ℝ) = Real.exp (-Real.exp 1) := by
  rw [ExpMinusExp.bias_coe]
  norm_num

example (p : unitInterval) (m : ℕ) :
    (ExpMinusExp.bias p m : ℝ) = Real.exp (-Real.exp ((m : ℝ) + p)) :=
  ExpMinusExp.bias_coe p m

#print axioms ExpMinusExp.expMinusExp_distSpec
#print axioms ExpMinusExp.twp_expMinusExp
#print axioms ExpMinusExp.bias_coe

end

end ExactFactoriesReview013
