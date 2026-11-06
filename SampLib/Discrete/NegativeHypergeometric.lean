import SampLib.Discrete.Laws.NegativeHypergeometric
import SampLib.Discrete.Hypergeometric
import SampLib.Core.SupportedSpec
import Samplers.Discrete.Urns

/-! # Failures before marked draws without replacement

Read a uniformly permuted labelled urn until the requested marked ball appears.
The first-color partition supplies the finite-population expectation recurrence.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.NegativeHypergeometric

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem valid_test (r ones : ℕ) (h : r ≤ ones) :
    decide ((ones : ℤ) < (r : ℤ)) = false := decide_eq_false (by omega)

private theorem pred_cast (n : ℕ) (h : 0 < n) :
    (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega

/-- Finite urn execution, with the sampled color supplying the recursive domain. -/
theorem twp_negativeHypergeometric (E : CoPset) (r ones zeros : ℕ) (h : r ≤ ones)
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂law r ones zeros) -∗
      tglWp E pl(&Occil.DiscreteExtra.negativeHypergeometric #int (r : ℤ)
        #int (ones : ℤ) #int (zeros : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  induction zeros using Nat.strong_induction_on generalizing r ones F with
  | h zeros ihz =>
    induction r generalizing ones F with
    | zero =>
      iintro Hcredit
      twp_pures
      twp_value
      imodintro
      iexists 0
      isimp only [expectation_zero] at Hcredit
      iframe Hcredit
      itrivial
    | succ r ihr =>
      have ho : 0 < ones := by omega
      have ht : 0 < ones + zeros := by omega
      have hcoin : IsDistSpec (GF := GF) E
          pl(&Occil.rationalCoin #int (ones : ℤ) #int ((ones : ℤ) + zeros))
          (RealCoin.law (Urn.bias ones zeros)) Val.bool := by
        simpa only [Urn.bias, dite_eq_left ht, Nat.cast_add] using
          RationalCoin.rationalCoin_distSpec (GF := GF) E ones (ones + zeros)
            (by omega) (by omega) (by omega)
      iintro Hcredit
      twp_pures
      rw [valid_test (r + 1) ones h]
      iterate 4 twp_pure
      simp only [RationalCoin.rationalCoin_closeRec, RationalCoin.rationalCoin_openRec]
      twp_bind pl(&Occil.rationalCoin #int (ones : ℤ) #int ((ones : ℤ) + zeros))
      isimp only [← expectation_coin r ones zeros ho F] at Hcredit
      iapply (hcoin.wp_supported (fun b => b = false → 0 < zeros)
        ((Set.to_countable _).measurableSet) (possible_failure ones zeros ho)
        (continuation r ones zeros F) (measurable_of_countable _) _) $$ Hcredit
      iintro %b %hb Hcredit
      cases b
      · have hz : 0 < zeros := hb rfl
        iterate 2 twp_pure
        rw [pred_cast zeros hz]
        twp_bind pl(&Occil.DiscreteExtra.negativeHypergeometric #int ((r + 1 : ℕ) : ℤ)
          #int (ones : ℤ) #int ((zeros - 1 : ℕ) : ℤ))
        iapply tglWp_wand
        isplitl [Hcredit]
        · isimp only [continuation, Bool.false_eq_true, ite_false] at Hcredit
          iapply (ihz (zeros - 1) (by omega) (r + 1) ones h (fun k => F (k + 1))) $$ Hcredit
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
      · iterate 3 twp_pure
        rw [Nat.cast_add_one, add_sub_cancel_right, pred_cast ones ho]
        twp_bind pl(&Occil.DiscreteExtra.negativeHypergeometric #int (r : ℤ)
          #int ((ones - 1 : ℕ) : ℤ) #int (zeros : ℤ))
        iapply (tglWp_mono fun _ => tglWp_value)
        isimp only [continuation, ite_true] at Hcredit
        iapply (ihr (ones - 1) (by omega) F) $$ Hcredit

/-- Typed negative-hypergeometric law for every feasible requested success count. -/
theorem negativeHypergeometric_distSpec (E : CoPset) (r ones zeros : ℕ) (h : r ≤ ones) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.negativeHypergeometric #int (r : ℤ)
      #int (ones : ℤ) #int (zeros : ℤ)) (law r ones zeros)
      (fun k : ℕ => Val.int (k : ℤ)) where
  spec F _ := wand_entails (twp_negativeHypergeometric E r ones zeros h F)

end specification

end

end SampLib.NegativeHypergeometric
