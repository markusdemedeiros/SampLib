import SampLib.Bernoulli.Laws.Complement
import SampLib.Uniform.RealCoin
import Samplers.Bernoulli.Basic
import Metrology.Iris.LocalBI

/-! # Complementing a biased coin -/

open Set ProbLang
open scoped ENNReal

namespace SampLib.Complement

noncomputable section

private theorem bool_not (b : Bool) : Bool.rec true false b = !b := by
  cases b <;> rfl

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- CTE specification for complement, including both endpoint biases. -/
theorem twp_complement (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ b, F b ∂law p) -∗ tglWp E pl(&Occil.complement &coin.fst #())
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  twp_pures
  twp_bind pl(&coin.fst #())
  isimp only [← expectation_preservation p F] at Hcredit
  iapply (hcoin.wp (fun b => F (!b)) (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  twp_pures
  twp_value
  imodintro
  iexists !b
  iframe Hcredit
  ipureintro
  simp only [Val.ext_iff, bool_not]

/-- The output bias is `1-p`. -/
theorem complement_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.complement &coin.fst #()) (law p) Val.bool where
  spec F _ := wand_entails (twp_complement E p coin hcoin F)

end specification

end

end SampLib.Complement
