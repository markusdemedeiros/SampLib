import SampLib.Bernoulli.Laws.CoinConditional
import SampLib.Uniform.RealCoin
import Samplers.Bernoulli.Basic
import Metrology.Iris.LocalBI

/-! # Conditional choice between two biased coins -/

open Set ProbLang
open scoped ENNReal

namespace SampLib.CoinConditional

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- CTE specification for abstract component and selector coins. -/
theorem twp_coinConditional (E : CoPset) (p q r : unitInterval)
    (left right select : Val rT)
    (hleft : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hright : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool)
    (hselect : IsDistSpec (GF := GF) E pl(&select.fst #()) (RealCoin.law r) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ b, F b ∂law p q r) -∗
      tglWp E pl(&Occil.coinConditional &left.fst &right.fst &select.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  twp_pures
  twp_bind pl(&select.fst #())
  isimp only [← expectation_preservation p q r F] at Hcredit
  iapply (hselect.wp (firstCredit p q F) (measurable_of_countable _) _) $$ Hcredit
  iintro %a Hcredit
  cases a
  · twp_pures
    isimp only [firstCredit, Bool.false_eq_true, ite_false] at Hcredit
    iapply hright.spec F (measurable_of_countable _) $$ Hcredit
  · twp_pures
    isimp only [firstCredit, ite_true] at Hcredit
    iapply hleft.spec F (measurable_of_countable _) $$ Hcredit

/-- Conditional mixing has bias `rp + (1-r)q`. -/
theorem coinConditional_distSpec (E : CoPset) (p q r : unitInterval)
    (left right select : Val rT)
    (hleft : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hright : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool)
    (hselect : IsDistSpec (GF := GF) E pl(&select.fst #()) (RealCoin.law r) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.coinConditional &left.fst &right.fst &select.fst #())
      (law p q r) Val.bool where
  spec F _ := wand_entails (twp_coinConditional E p q r left right select hleft hright hselect F)

end specification

end

end SampLib.CoinConditional
