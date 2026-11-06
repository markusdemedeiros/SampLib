import SampLib.Bernoulli.Laws.BernoulliRace
import SampLib.Uniform.FairCoin
import Samplers.Bernoulli.Basic
import Metrology.Iris.LocalBI

/-! # Bernoulli race

A fair selector chooses which input coin to try. Success returns that side;
failure retries. The output bias is `p / (p + q)` whenever `p + q > 0`.
-/

open Set ProbLang
open scoped ENNReal NNReal

namespace SampLib.BernoulliRace

open RealCoin (lintegral_law)

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The race is total when at least one input coin can succeed. -/
theorem twp_bernoulliRace (E : CoPset) (p q : unitInterval) (hsum : 0 < (p : ℝ) + q)
    (left right : Val rT)
    (hleft : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hright : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (credit p q F) -∗ tglWp E pl(&Occil.bernoulliRace &left.fst &right.fst #())
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε (one_lt_factor p q hsum) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  twp_pure
  twp_pure
  twp_pure
  twp_pure
  simp only [FairCoin.fairCoin_closeRec, FairCoin.fairCoin_openRec]
  twp_bind pl(&Occil.fairCoin #())
  icombine Hcredit Hterm as Htotal
  ihave Hsample := ErrorCredit.weaken (expectation p q hsum F ε) $$ Htotal
  iapply ((FairCoin.fairCoin_distSpec E).wp (fairCredit p q F ε)
    (measurable_of_countable _) _) $$ Hsample
  iintro %side Hcredit
  cases side
  · twp_pures
    twp_bind pl(&right.fst #())
    isimp only [fairCredit, Bool.false_eq_true, ite_false] at Hcredit
    iapply (hright.wp (coinCredit p q F ε false) (measurable_of_countable _) _) $$ Hcredit
    iintro %success Hcredit
    cases success
    · twp_pure
      isimp only [coinCredit, Bool.false_eq_true, ite_false] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      twp_bind pl(&Occil.bernoulliRace &left.fst &right.fst #())
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply IH $$ Hterm Hcredit
    · twp_pures
      twp_value
      imodintro
      iexists false
      isimp only [coinCredit, ite_true] at Hcredit
      iframe Hcredit
      itrivial
  · twp_pures
    twp_bind pl(&left.fst #())
    isimp only [fairCredit, ite_true] at Hcredit
    iapply (hleft.wp (coinCredit p q F ε true) (measurable_of_countable _) _) $$ Hcredit
    iintro %success Hcredit
    cases success
    · twp_pure
      isimp only [coinCredit, Bool.false_eq_true, ite_false] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      twp_bind pl(&Occil.bernoulliRace &left.fst &right.fst #())
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply IH $$ Hterm Hcredit
    · twp_pures
      twp_value
      imodintro
      iexists true
      isimp only [coinCredit, ite_true] at Hcredit
      iframe Hcredit
      itrivial

/-- Typed ratio specification, including zero probability on either individual side. -/
theorem bernoulliRace_distSpec (E : CoPset) (p q : unitInterval) (hsum : 0 < (p : ℝ) + q)
    (left right : Val rT)
    (hleft : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hright : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.bernoulliRace &left.fst &right.fst #())
      (law p q) Val.bool where
  spec F _ := by
    simpa only [lintegral_law] using
      wand_entails (twp_bernoulliRace E p q hsum left right hleft hright F)

end specification

end

end SampLib.BernoulliRace
