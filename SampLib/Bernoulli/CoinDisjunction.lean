import SampLib.Uniform.RealCoin
import Samplers.Bernoulli.Basic
import Metrology.Iris.LocalBI

/-! # Disjunction of two biased coins -/

open Set ProbLang
open ENNReal (ofReal ofReal_add ofReal_mul)
open scoped ENNReal

namespace SampLib.CoinDisjunction

noncomputable section

/-- Bias `1-(1-p)(1-q)`. -/
abbrev bias (p q : unitInterval) :=
  unitInterval.symm (unitInterval.symm p * unitInterval.symm q)

abbrev law (p q : unitInterval) := RealCoin.law (bias p q)

def firstCredit (q : unitInterval) (F : Bool → ℝ≥0∞) (a : Bool) : ℝ≥0∞ :=
  if a then F true else ∫⁻ b, F b ∂RealCoin.law q

/-- The success mass is `p + (1-p)q = 1-(1-p)(1-q)`. -/
theorem expectation_preservation (p q : unitInterval) (F : Bool → ℝ≥0∞) :
    ∫⁻ a, firstCredit q F a ∂RealCoin.law p = ∫⁻ b, F b ∂law p q := by
  have htrue : 1 - (1 - (p : ℝ)) * (1 - q) = p + (1 - p) * (q : ℝ) := by ring
  simp [law, bias, firstCredit, RealCoin.lintegral_law, RealCoin.credit,
    RealCoin.pmf, unitInterval.coe_symm_eq]
  rw [htrue, ofReal_add p.2.1 (mul_nonneg (sub_nonneg.mpr p.2.2) q.2.1),
    ofReal_mul (sub_nonneg.mpr p.2.2)]
  simp only [ofReal_mul (sub_nonneg.mpr p.2.2)]
  ring

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- CTE specification for two abstract input coins. -/
theorem twp_coinDisjunction (E : CoPset) (p q : unitInterval) (left right : Val rT)
    (hleft : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hright : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ b, F b ∂law p q) -∗
      tglWp E pl(&Occil.coinDisjunction &left.fst &right.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  twp_pures
  twp_bind pl(&left.fst #())
  isimp only [← expectation_preservation p q F] at Hcredit
  iapply (hleft.wp (firstCredit q F) (measurable_of_countable _) _) $$ Hcredit
  iintro %a Hcredit
  cases a
  · twp_pures
    isimp only [firstCredit, Bool.false_eq_true, ite_false] at Hcredit
    iapply hright.spec F (measurable_of_countable _) $$ Hcredit
  · twp_pures
    twp_value
    imodintro
    iexists true
    isimp only [firstCredit, ite_true] at Hcredit
    iframe Hcredit
    itrivial

/-- The output bias is `p+q-pq`. -/
theorem coinDisjunction_distSpec (E : CoPset) (p q : unitInterval) (left right : Val rT)
    (hleft : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hright : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.coinDisjunction &left.fst &right.fst #())
      (law p q) Val.bool where
  spec F _ := wand_entails (twp_coinDisjunction E p q left right hleft hright F)

end specification

end

end SampLib.CoinDisjunction
