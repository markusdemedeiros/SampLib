import SampLib.Discrete.Laws.Hypergeometric
import SampLib.Common.Laws.Urn
import SampLib.Combinatorial.SampleWithoutReplacement
import Metrology.Iris.LocalBI

/-! # Hypergeometric sampling

The law counts marked balls in a uniform ordered selection of distinct labelled
balls. Partitioning those selections by the first ball gives the urn recurrence.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.Hypergeometric

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem valid_test (n ones zeros : ℕ) (h : n ≤ ones + zeros) :
    decide ((ones : ℤ) + zeros < n) = false := by
  exact decide_eq_false (by omega)

private theorem pred_cast (n : ℕ) (h : 0 < n) :
    (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega

/-- Finite urn sampling, including exhausted colors and the empty zero-draw urn. -/
theorem twp_hypergeometric (E : CoPset) (n ones zeros : ℕ) (h : n ≤ ones + zeros)
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂law n ones zeros) -∗
      tglWp E pl(&Occil.hypergeometric #int (n : ℤ) #int (ones : ℤ) #int (zeros : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  induction n generalizing ones zeros F with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists 0
    isimp only [expectation_zero] at Hcredit
    iframe Hcredit
    itrivial
  | succ n ih =>
    have ht : 0 < ones + zeros := by omega
    have hcoin : IsDistSpec (GF := GF) E
        pl(&Occil.rationalCoin #int (ones : ℤ) #int ((ones : ℤ) + zeros))
        (RealCoin.law (Urn.bias ones zeros)) Val.bool := by
      simpa only [Urn.bias, dite_eq_left ht, Nat.cast_add] using
        RationalCoin.rationalCoin_distSpec (GF := GF) E ones (ones + zeros)
          (by omega) (by omega) (by omega)
    iintro Hcredit
    twp_pures
    simp only [Bool.false_or, valid_test (n + 1) ones zeros h]
    iterate 4 twp_pure
    simp only [RationalCoin.rationalCoin_closeRec, RationalCoin.rationalCoin_openRec]
    twp_bind pl(&Occil.rationalCoin #int (ones : ℤ) #int ((ones : ℤ) + zeros))
    isimp only [← expectation_coin n ones zeros ht F] at Hcredit
    iapply (hcoin.wp (continuation n ones zeros F) (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    cases b
    · by_cases hz : zeros = 0
      · isimp only [continuation, Bool.false_eq_true, ite_false, hz, ite_true] at Hcredit
        iexfalso
        iapply (ErrorCredit.contradict (ε := ∞) le_top) $$ Hcredit
      · iterate 3 twp_pure
        rw [Nat.cast_add_one, add_sub_cancel_right, pred_cast zeros (by omega)]
        simp only [Exp.ofVal]
        twp_bind pl(&Occil.hypergeometric #int (n : ℤ) #int (ones : ℤ)
          #int ((zeros - 1 : ℕ) : ℤ))
        iapply tglWp_wand
        isplitl [Hcredit]
        · isimp only [continuation, Bool.false_eq_true, ite_false, hz] at Hcredit
          iapply (ih ones (zeros - 1) (by omega) F) $$ Hcredit
        iintro %v ⟨%k, %hv, Hcredit⟩
        iapply (tglWp_value (v := v))
        iexists k
        iframe Hcredit
        ipureintro
        exact hv
    · by_cases ho : ones = 0
      · isimp only [continuation, ite_true, ho, ite_false] at Hcredit
        iexfalso
        iapply (ErrorCredit.contradict (ε := ∞) le_top) $$ Hcredit
      · iterate 3 twp_pure
        rw [Nat.cast_add_one, add_sub_cancel_right, pred_cast ones (by omega)]
        simp only [Exp.ofVal]
        twp_bind pl(&Occil.hypergeometric #int (n : ℤ) #int ((ones - 1 : ℕ) : ℤ)
          #int (zeros : ℤ))
        iapply tglWp_wand
        isplitl [Hcredit]
        · isimp only [continuation, ite_true, ho, ite_false] at Hcredit
          iapply (ih (ones - 1) zeros (by omega) (fun k => F (k + 1))) $$ Hcredit
        iintro %v ⟨%k, %hv, Hcredit⟩
        subst v
        twp_pures
        twp_value
        imodintro
        iexists k + 1
        iframe Hcredit
        ipureintro
        apply Val.ext
        simp [add_comm]

/-- Typed hypergeometric law on the full feasible urn domain. -/
theorem hypergeometric_distSpec (E : CoPset) (n ones zeros : ℕ)
    [Fact (n ≤ ones + zeros)] :
    IsDistSpec (GF := GF) E
      pl(&Occil.hypergeometric #int (n : ℤ) #int (ones : ℤ) #int (zeros : ℤ))
      (law n ones zeros) (fun k : ℕ => Val.int (k : ℤ)) where
  spec F _ := wand_entails (twp_hypergeometric E n ones zeros Fact.out F)

end specification

end

end SampLib.Hypergeometric
