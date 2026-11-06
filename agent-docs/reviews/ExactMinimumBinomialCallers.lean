import SampLib.Bernoulli.Support.MinimumComplementBinomial

open ProbLang
open scoped ENNReal

namespace ExactMinimumBinomialCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (m : ℕ) (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (RealCoin.credit (MinimumComplement.conditionalBias p m) F) ∗ I -∗
      tglWp E (MinimumComplement.binomialBody coin m)
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply MinimumComplement.twp_binomialBody E p coin hcoin m F $$ Hcredit
  iintro %v ⟨%b, %hv, Hcredit⟩
  iexists b
  iframe Hcredit HI
  ipureintro
  exact hv

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (m : ℕ) (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (RealCoin.credit (MinimumComplement.conditionalBias p m) F) ∗ I -∗
      tglWp E pl(&MinimumComplement.binomialStage &coin.fst #int (m : ℤ))
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply MinimumComplement.twp_binomialStage E p coin hcoin m F $$ Hcredit
  iintro %v ⟨%b, %hv, Hcredit⟩
  iexists b
  iframe Hcredit HI
  ipureintro
  exact hv

example (p : unitInterval) : (MinimumComplement.conditionalBias p 0 : ℝ) = 1 / 2 := by
  simp [MinimumComplement.conditionalBias]

example (m : ℕ) (hm : 0 < m) : (MinimumComplement.conditionalBias 0 m : ℝ) = 0 := by
  simp [MinimumComplement.conditionalBias, hm.ne']

#print axioms SampLib.MinimumComplement.twp_binomialBody
#print axioms SampLib.MinimumComplement.twp_binomialStage
#print axioms SampLib.MinimumComplement.binomial_expectation

end

end ExactMinimumBinomialCallers
