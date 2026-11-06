import SampLib.Discrete.Laws.Binomial
import SampLib.Uniform.RealCoin
import Samplers.Discrete
import Metrology.Iris.LocalBI

/-! # Binomial trial sums

The CTE proof splits the expected credit on the first coin flip, recurses on the
remaining trials, and adds the flip to the returned count.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.Binomial

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_binomial (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (n : ℕ) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂law p n) -∗ tglWp E pl(&Occil.binomial &coin.fst #int (n : ℤ))
      (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  induction n generalizing F with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists 0
    isimp only [expectation_zero] at Hcredit
    iframe Hcredit
    itrivial
  | succ n IH =>
    iintro Hcredit
    twp_pures
    twp_bind pl(&coin.fst #())
    isimp only [← expectation p n F] at Hcredit
    iapply (hcoin.wp (continuation p n F) (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    twp_pure
    twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    twp_bind pl(&Occil.binomial &coin.fst #int (n : ℤ))
    iapply tglWp_wand
    isplitl [Hcredit]
    · isimp only [continuation] at Hcredit
      iapply IH $$ Hcredit
    iintro %v ⟨%k, %hv, Hcredit⟩
    subst v
    cases b
    · twp_pures
      twp_value
      imodintro
      iexists k
      isimp only [Bool.false_eq_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pures
      rw [← Nat.cast_add_one]
      twp_value
      imodintro
      iexists (k + 1)
      isimp only [ite_true] at Hcredit
      iframe Hcredit
      itrivial

/-- Typed binomial specification for every trial count and both coin endpoints. -/
theorem binomial_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (n : ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.binomial &coin.fst #int (n : ℤ))
      (law p n) (fun k => Val.int (k : ℤ)) where
  spec F _ := wand_entails (twp_binomial E p coin hcoin n F)

end specification

end

end SampLib.Binomial
