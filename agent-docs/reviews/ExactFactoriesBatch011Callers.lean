import SampLib.Bernoulli.FractionalPower

open ProbLang
open scoped ENNReal

namespace ExactFactoriesReview011

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

example (E : CoPset) (p : unitInterval) (a b : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (FractionalPower.fractionalPower_distSpec E p a b ha hab coin hcoin) F I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool)
    (I : IProp GF) :=
  frame (FractionalPower.fractionalPower_distSpec E 0 1 2
    (by norm_num) (by norm_num) coin hcoin) (fun b => if b then ∞ else 0) I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 1) Val.bool)
    (I : IProp GF) :=
  frame (FractionalPower.fractionalPower_distSpec E 1 1 2
    (by norm_num) (by norm_num) coin hcoin) (fun b => if b then 0 else ∞) I

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (FractionalPower.fractionalPower_distSpec E p 1 1
    (by norm_num) (by norm_num) coin hcoin) F I

example : (FractionalPower.bias 0 1 2 (by norm_num) (by norm_num) : ℝ) = 0 := by
  norm_num [FractionalPower.bias, FractionalPower.powerBias, FractionalPower.exponent]

example : (FractionalPower.bias 1 1 2 (by norm_num) (by norm_num) : ℝ) = 1 := by
  norm_num [FractionalPower.bias, FractionalPower.powerBias, FractionalPower.exponent]

example (p : unitInterval) :
    (FractionalPower.bias p 1 1 (by norm_num) (by norm_num) : ℝ) = p := by
  simp [FractionalPower.bias, FractionalPower.powerBias, FractionalPower.exponent]

example : RealCoin.credit (FractionalPower.bias 0 1 2 (by norm_num) (by norm_num))
    (fun b => if b then ∞ else 0) = 0 := by
  have h : FractionalPower.bias 0 1 2 (by norm_num) (by norm_num) = 0 :=
    Subtype.ext (by
      norm_num [FractionalPower.bias, FractionalPower.powerBias, FractionalPower.exponent])
  simp [h, RealCoin.credit, RealCoin.pmf]

#print axioms FractionalPower.fractionalPower_distSpec
#print axioms FractionalPower.twp_loop
#print axioms FractionalPower.tailCredit_zero
#print axioms FractionalPower.round_expectation
#print axioms FractionalPower.survival_tendsto_zero
#print axioms FractionalPower.successMass_tsum
#print axioms AbsorbingChain.twp_of_survival

end

end ExactFactoriesReview011
