import SampLib.Core.Retry
import SampLib.Bernoulli.Laws.OneDivOnePlus
import SampLib.Uniform.FairCoin
import Samplers.Bernoulli.Basic
import Metrology.Iris.LocalBI

/-! # Reciprocal Bernoulli factory

A fair flip either returns `true`, or tests the input coin and retries on failure.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.OneDivOnePlus

open RealCoin (lintegral_law)

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The reciprocal factory is total for every input bias, including both endpoints. -/
theorem twp_oneDivOnePlus (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (credit p F) -∗ tglWp E pl(&Occil.oneDivOnePlus &coin.fst #())
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iapply Retry.twp_loop (k := 2) solve_not_value (by norm_num)
  iintro !> %ε %hε IH Hcredit
  isimp only [ENNReal.coe_ofNat] at IH
  twp_pure
  twp_pure
  twp_pure
  simp only [FairCoin.fairCoin_closeRec, FairCoin.fairCoin_openRec]
  twp_bind pl(&Occil.fairCoin #())
  ihave Hsample := ErrorCredit.weaken (expectation p F ε) $$ Hcredit
  iapply ((FairCoin.fairCoin_distSpec E).wp (fairCredit p F ε)
    (measurable_of_countable _) _) $$ Hsample
  iintro %b Hcredit
  cases b
  · twp_pures
    twp_bind pl(&coin.fst #())
    isimp only [fairCredit, Bool.false_eq_true, ite_false] at Hcredit
    iapply (hcoin.wp (coinCredit p F ε) (measurable_of_countable _) _) $$ Hcredit
    iintro %a Hcredit
    cases a
    · twp_pure
      isimp only [coinCredit, Bool.false_eq_true, ite_false] at Hcredit
      twp_bind pl(&Occil.oneDivOnePlus &coin.fst #())
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply IH $$ Hcredit
    · twp_pures
      twp_value
      imodintro
      iexists false
      isimp only [coinCredit, ite_true] at Hcredit
      iframe Hcredit
      itrivial
  · twp_pures
    twp_value
    imodintro
    iexists true
    isimp only [fairCredit, ite_true] at Hcredit
    iframe Hcredit
    itrivial

/-- Typed distribution specification. -/
theorem oneDivOnePlus_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.oneDivOnePlus &coin.fst #()) (law p) Val.bool where
  spec F _ := by
    simpa only [lintegral_law] using wand_entails (twp_oneDivOnePlus E p coin hcoin F)

end specification

end

end SampLib.OneDivOnePlus
