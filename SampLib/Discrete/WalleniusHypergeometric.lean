import SampLib.Discrete.Laws.Wallenius
import SampLib.Core.SupportedSpec
import SampLib.Core.ProofMode.BindFrom
import Samplers.Discrete.Urns

/-! # Two-color Wallenius sampling without replacement

The canonical color-word likelihood supplies the first-draw expectation.
The selected color remains nonempty, so the recursive request stays feasible.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.WalleniusHypergeometric

noncomputable section

abbrev law := Wallenius.twoColorLaw

private theorem request_test (n ones zeros : ℕ) (hn : n + 1 ≤ ones + zeros) :
    decide ((ones : ℤ) + zeros < (n : ℤ) + 1) = false := decide_eq_false (by omega)

private theorem positive_test (a : ℕ) (ha : 0 < a) :
    decide ((a : ℤ) ≤ 0) = false := by simp [Nat.ne_of_gt ha]

private theorem total_pos (n ones zeros a b : ℕ) (hn : n + 1 ≤ ones + zeros)
    (ha : 0 < a) (hb : 0 < b) : 0 < ones * a + zeros * b := by
  have h := Wallenius.request_weight_pos [ones, zeros] [a, b] n
    (by simpa using hn) rfl (by simp [ha, hb])
  simpa [Wallenius.weights] using h

private theorem marked_request (n ones zeros : ℕ) (hn : n + 1 ≤ ones + zeros)
    (ho : 0 < ones) : n ≤ ones - 1 + zeros := by omega

private theorem unmarked_request (n ones zeros : ℕ) (hn : n + 1 ≤ ones + zeros)
    (hz : 0 < zeros) : n ≤ ones + (zeros - 1) := by omega

private theorem pred_cast (n : ℕ) (hn : 0 < n) :
    (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega

private theorem marked_cast (k : ℕ) : (1 : ℤ) + k = ((k + 1 : ℕ) : ℤ) := by omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] RationalCoin.rationalCoin_openRec RationalCoin.rationalCoin_closeRec

private theorem coin_distSpec (E : CoPset) (ones zeros a b : ℕ)
    (hs : 0 < ones * a + zeros * b) :
    IsDistSpec (GF := GF) E pl(&Occil.rationalCoin #int ((ones : ℤ) * a)
      #int ((ones : ℤ) * a + (zeros : ℤ) * b))
      (RealCoin.law (Urn.bias (ones * a) (zeros * b))) Val.bool := by
  simpa only [Urn.bias, dite_eq_left hs, Nat.cast_add, Nat.cast_mul] using
    RationalCoin.rationalCoin_distSpec (GF := GF) E (ones * a) (ones * a + zeros * b)
      (by positivity) (by exact_mod_cast hs) (by omega)

/-- Each weighted draw spends the expectation of the remaining canonical urn. -/
theorem twp_walleniusHypergeometric (E : CoPset) (n ones zeros a b : ℕ)
    (hn : n ≤ ones + zeros) (ha : 0 < a) (hb : 0 < b) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂law n ones zeros a b) -∗
      tglWp E pl(&Occil.DiscreteExtra.walleniusHypergeometric #int (n : ℤ)
        #int (ones : ℤ) #int (zeros : ℤ) #int (a : ℤ) #int (b : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  induction n generalizing ones zeros F with
  | zero =>
    iintro Hcredit
    isimp [Occil.DiscreteExtra.walleniusHypergeometric, Exp.close, Exp.closeRec]
    twp_pures
    simp only [positive_test a ha, positive_test b hb, Bool.or_false]
    twp_pures
    twp_value
    imodintro
    iexists 0
    isimp only [law, Wallenius.twoColor_zero, MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    itrivial
  | succ n ih =>
    have hs := total_pos n ones zeros a b hn ha hb
    have hcoin := coin_distSpec (rT := rT) (GF := GF) E ones zeros a b hs
    iintro Hcredit
    isimp [Occil.DiscreteExtra.walleniusHypergeometric, Exp.close, Exp.closeRec]
    twp_pures
    simp only [request_test n ones zeros hn, positive_test a ha, positive_test b hb,
      Bool.or_false]
    iterate 7 twp_pure
    twp_bind pl(&Occil.rationalCoin #int ((ones : ℤ) * a)
      #int ((ones : ℤ) * a + (zeros : ℤ) * b))
    isimp only [← Wallenius.twoColor_expectation n ones zeros a b hn ha hb F] at Hcredit
    iapply (hcoin.wp_supported (fun marked => if marked then 0 < ones else 0 < zeros)
      (Set.to_countable _).measurableSet (Wallenius.coin_selected ones zeros a b hs)
      (fun marked => if marked then ∫⁻ k, F (k + 1) ∂law n (ones - 1) zeros a b
        else ∫⁻ k, F k ∂law n ones (zeros - 1) a b)
      (measurable_of_countable _) _) $$ Hcredit
    iintro %marked %hselected Hcredit
    cases marked with
    | false =>
      have hz : 0 < zeros := hselected
      iterate 3 twp_pure
      simp only [add_sub_cancel_right, pred_cast zeros hz]
      isimp only [Bool.false_eq_true, ite_false] at Hcredit
      have hnext := ih ones (zeros - 1) (unmarked_request n ones zeros hn hz) F
      simp [Occil.DiscreteExtra.walleniusHypergeometric, Exp.close, Exp.closeRec] at hnext
      exact wand_entails hnext
    | true =>
      have ho : 0 < ones := hselected
      iterate 3 twp_pure
      simp only [add_sub_cancel_right, pred_cast ones ho]
      isimp only [ite_true] at Hcredit
      have hnext := ih (ones - 1) zeros (marked_request n ones zeros hn ho) (fun k => F (k + 1))
      simp [Occil.DiscreteExtra.walleniusHypergeometric, Exp.close, Exp.closeRec] at hnext
      twp_bind_from hnext
      iapply tglWp_wand
      isplitl [Hcredit]
      · exact wand_entails hnext
      iintro %v ⟨%k, %hv, Hcredit⟩
      subst v
      twp_pures
      twp_value
      imodintro
      iexists k + 1
      iframe Hcredit
      ipureintro
      exact congrArg Val.int (marked_cast k)

/-- Every feasible natural request and every pair of positive rational odds. -/
theorem walleniusHypergeometric_distSpec (E : CoPset) (n ones zeros a b : ℕ)
    (hn : n ≤ ones + zeros) (ha : 0 < a) (hb : 0 < b) :
    IsDistSpec (GF := GF) E
      pl(&Occil.DiscreteExtra.walleniusHypergeometric #int (n : ℤ) #int (ones : ℤ)
        #int (zeros : ℤ) #int (a : ℤ) #int (b : ℤ)) (law n ones zeros a b)
      (fun k : ℕ => Val.int (k : ℤ)) where
  spec F _ := wand_entails (twp_walleniusHypergeometric E n ones zeros a b hn ha hb F)

omit [ProbLangDist.IsUniformInt rT] in
/-- Zero draws still validate the odds, but use no random primitive. -/
theorem walleniusHypergeometric_zero_distSpec (E : CoPset) (ones zeros a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.walleniusHypergeometric #0
      #int (ones : ℤ) #int (zeros : ℤ) #int (a : ℤ) #int (b : ℤ))
      (MeasureTheory.Measure.dirac (0 : ℕ)) (fun k : ℕ => Val.int (k : ℤ)) where
  spec F _ := by
    iintro Hcredit
    isimp [Occil.DiscreteExtra.walleniusHypergeometric, Exp.close, Exp.closeRec]
    twp_pures
    simp only [positive_test a ha, positive_test b hb, Bool.or_false]
    twp_pures
    twp_value
    imodintro
    iexists 0
    isimp only [MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    itrivial

end specification

end

end SampLib.WalleniusHypergeometric
