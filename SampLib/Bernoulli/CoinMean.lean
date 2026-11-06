import SampLib.Bernoulli.Laws.CoinMean
import SampLib.Bernoulli.CoinConditional
import SampLib.Uniform.FairCoin
import Metrology.Iris.LocalBI

/-! # Arithmetic mean of two coin probabilities -/

open Set ProbLang
open scoped ENNReal

namespace SampLib.CoinMean

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- CTE specification using the verified integer fair coin. -/
theorem twp_coinMean (E : CoPset) (p q : unitInterval) (left right : Val rT)
    (hleft : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hright : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ b, F b ∂law p q) -∗
      tglWp E pl(&Occil.coinMean &left.fst &right.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  twp_pure
  twp_pure
  twp_pure
  twp_bind pl(&Occil.fairCoin #())
  isimp only [← expectation_preservation p q F] at Hcredit
  iapply ((FairCoin.fairCoin_distSpec E).wp (CoinConditional.firstCredit p q F)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %a Hcredit
  cases a
  · twp_pures
    isimp only [CoinConditional.firstCredit, Bool.false_eq_true, ite_false] at Hcredit
    iapply hright.spec F (measurable_of_countable _) $$ Hcredit
  · twp_pures
    isimp only [CoinConditional.firstCredit, ite_true] at Hcredit
    iapply hleft.spec F (measurable_of_countable _) $$ Hcredit

/-- The output bias is `(p+q)/2`. -/
theorem coinMean_distSpec (E : CoPset) (p q : unitInterval) (left right : Val rT)
    (hleft : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hright : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.coinMean &left.fst &right.fst #())
      (law p q) Val.bool where
  spec F _ := wand_entails (twp_coinMean E p q left right hleft hright F)

end specification

end

end SampLib.CoinMean
