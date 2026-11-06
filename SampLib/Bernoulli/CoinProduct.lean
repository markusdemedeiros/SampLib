import SampLib.Uniform.RealCoin
import Samplers.Bernoulli.Basic
import Metrology.Iris.LocalBI

/-! # Product of two biased coins -/

open Set ProbLang
open ENNReal (ofReal ofReal_add ofReal_mul)
open scoped ENNReal

namespace SampLib.CoinProduct

noncomputable section

abbrev law (p q : unitInterval) := RealCoin.law (p * q)

/-- Credit for the second draw is needed only after a successful first draw. -/
def firstCredit (q : unitInterval) (F : Bool → ℝ≥0∞) (a : Bool) : ℝ≥0∞ :=
  if a then ∫⁻ b, F b ∂RealCoin.law q else F false

/-- The failure mass is `p(1-q) + (1-p) = 1-pq`. -/
theorem expectation_preservation (p q : unitInterval) (F : Bool → ℝ≥0∞) :
    ∫⁻ a, firstCredit q F a ∂RealCoin.law p = ∫⁻ b, F b ∂law p q := by
  have hfalse : 1 - (p : ℝ) * q = (p : ℝ) * (1 - q) + (1 - p) := by ring
  simp [law, firstCredit, RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]
  rw [hfalse, ofReal_add (mul_nonneg p.2.1 (sub_nonneg.mpr q.2.2))
    (sub_nonneg.mpr p.2.2)]
  simp only [ofReal_mul p.2.1]
  ring

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- CTE specification for two abstract input coins. -/
theorem twp_coinProduct (E : CoPset) (p q : unitInterval) (left right : Val rT)
    (hleft : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hright : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ b, F b ∂law p q) -∗
      tglWp E pl(&Occil.coinProduct &left.fst &right.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  twp_pures
  twp_bind pl(&left.fst #())
  isimp only [← expectation_preservation p q F] at Hcredit
  iapply (hleft.wp (firstCredit q F) (measurable_of_countable _) _) $$ Hcredit
  iintro %a Hcredit
  cases a
  · twp_pures
    twp_value
    imodintro
    iexists false
    isimp only [firstCredit, Bool.false_eq_true, ite_false] at Hcredit
    iframe Hcredit
    itrivial
  · twp_pures
    isimp only [firstCredit, ite_true] at Hcredit
    iapply hright.spec F (measurable_of_countable _) $$ Hcredit

/-- The output bias is `pq`. -/
theorem coinProduct_distSpec (E : CoPset) (p q : unitInterval) (left right : Val rT)
    (hleft : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hright : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.coinProduct &left.fst &right.fst #())
      (law p q) Val.bool where
  spec F _ := wand_entails (twp_coinProduct E p q left right hleft hright F)

end specification

end

end SampLib.CoinProduct
