import SampLib.Bernoulli.Laws.EvenParity
import SampLib.Uniform.RealCoin
import SampLib.Core.Retry
import Samplers.Bernoulli.Basic
import Metrology.Iris.LocalBI

/-! # Even-parity Bernoulli factory

Pairs of successes retry. The output bias is `1 / (1 + p)` for `p < 1`.
-/

open Set ProbLang
open scoped ENNReal NNReal

namespace SampLib.EvenParity

open RealCoin (lintegral_law)

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The parity factory is total for `p < 1`, including `p = 0`. -/
theorem twp_evenParity (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hp : (p : ℝ) < 1)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (credit p F) -∗ tglWp E pl(&Occil.evenParity &coin.fst #())
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iapply Retry.twp_loop solve_not_value (one_lt_factor p hp)
  iintro !> %ε %hε IH Hcredit
  twp_pures
  twp_bind pl(&coin.fst #())
  ihave Hsample := ErrorCredit.weaken (expectation p F ε) $$ Hcredit
  iapply (hcoin.wp (firstCredit p F ε) (measurable_of_countable _) _) $$ Hsample
  iintro %a Hcredit
  cases a
  · twp_pures
    twp_value
    imodintro
    iexists true
    isimp only [firstCredit, Bool.false_eq_true, ite_false] at Hcredit
    iframe Hcredit
    itrivial
  · twp_pures
    twp_bind pl(&coin.fst #())
    isimp only [firstCredit, ite_true] at Hcredit
    iapply (hcoin.wp (pairCredit p F ε true) (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    cases b
    · twp_pures
      twp_value
      imodintro
      iexists false
      isimp only [pairCredit, Bool.false_eq_true, ite_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pure
      isimp only [pairCredit, ite_true] at Hcredit
      twp_bind pl(&Occil.evenParity &coin.fst #())
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply IH $$ Hcredit

/-- Typed distribution specification. -/
theorem evenParity_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hp : (p : ℝ) < 1)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.evenParity &coin.fst #()) (law p) Val.bool where
  spec F _ := by
    simpa only [lintegral_law, credit] using
      wand_entails (twp_evenParity E p coin hp hcoin F)

end specification

end

end SampLib.EvenParity
