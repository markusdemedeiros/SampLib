import SampLib.Uniform.RealCoin
import SampLib.Continuous.Laws.IterateCoin
import Samplers.Continuous
import Metrology.Iris.LocalBI

/-! # Finite Bernoulli iteration

All `n` input flips must succeed. The expectation recurrence factors the success
probability as `p * p^n`; finite induction supplies total correctness.
-/

open Set ProbLang
open ENNReal (ofReal ofReal_add ofReal_mul ofReal_pow)
open scoped ENNReal

namespace SampLib.IterateCoin

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_iterateCoin (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (n : ℕ) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (credit p n F) -∗ tglWp E pl(&Occil.iterateCoin &coin.fst #int (n : ℤ))
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  induction n generalizing F with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists true
    isimp only [credit_zero] at Hcredit
    iframe Hcredit
    itrivial
  | succ n IH =>
    iintro Hcredit
    twp_pures
    twp_bind pl(&coin.fst #())
    isimp only [← expectation p n F] at Hcredit
    iapply (hcoin.wp (continuation p n F) (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    cases b
    · twp_pures
      twp_value
      imodintro
      iexists false
      isimp only [continuation, Bool.false_eq_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pure
      twp_pure
      rw [Nat.cast_add_one, add_sub_cancel_right]
      twp_bind pl(&Occil.iterateCoin &coin.fst #int (n : ℤ))
      iapply (tglWp_mono fun _ => tglWp_value)
      isimp only [continuation, ite_true] at Hcredit
      iapply IH $$ Hcredit

/-- Typed specification for the all-successes factory, including both coin endpoints. -/
theorem iterateCoin_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (n : ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.iterateCoin &coin.fst #int (n : ℤ))
      (law p n) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law, credit] using
      wand_entails (twp_iterateCoin E p coin hcoin n F)

end specification

end

end SampLib.IterateCoin
