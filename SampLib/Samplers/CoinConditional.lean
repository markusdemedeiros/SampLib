import SampLib.Samplers.RealCoin
import Samplers.Bernoulli.Basic
import Metrology.Iris.LocalBI

/-! # Conditional choice between two biased coins -/

open Set ProbLang
open ENNReal (ofReal ofReal_add ofReal_mul)
open scoped ENNReal

namespace SampLib.CoinConditional

noncomputable section

/-- Bias `(1-r)q + rp`, with `r` the selector's probability. -/
abbrev bias (p q r : unitInterval) := Set.Icc.convexComb q p r

abbrev law (p q r : unitInterval) := RealCoin.law (bias p q r)

def firstCredit (p q : unitInterval) (F : Bool → ℝ≥0∞) (a : Bool) : ℝ≥0∞ :=
  if a then ∫⁻ b, F b ∂RealCoin.law p else ∫⁻ b, F b ∂RealCoin.law q

/-- The selector mixes the two success and failure masses with weights `r` and `1-r`. -/
theorem expectation_preservation (p q r : unitInterval) (F : Bool → ℝ≥0∞) :
    ∫⁻ a, firstCredit p q F a ∂RealCoin.law r = ∫⁻ b, F b ∂law p q r := by
  have hfalse : 1 - ((1 - (r : ℝ)) * q + r * p) =
      (1 - r) * (1 - (q : ℝ)) + r * (1 - (p : ℝ)) := by ring
  simp [law, bias, firstCredit, RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]
  rw [hfalse,
    ofReal_add (mul_nonneg (sub_nonneg.mpr r.2.2) q.2.1) (mul_nonneg r.2.1 p.2.1),
    ofReal_add (mul_nonneg (sub_nonneg.mpr r.2.2) (sub_nonneg.mpr q.2.2))
      (mul_nonneg r.2.1 (sub_nonneg.mpr p.2.2))]
  simp only [ofReal_mul (sub_nonneg.mpr r.2.2), ofReal_mul r.2.1]
  ring

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
