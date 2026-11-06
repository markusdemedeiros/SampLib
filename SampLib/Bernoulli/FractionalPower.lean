import SampLib.Bernoulli.Laws.FractionalPower
import SampLib.Common.Syntax.FractionalPower

/-! # Mendo's fractional-power Bernoulli factory

Each round tests the input coin and then a reciprocal hazard. The generalized
binomial law supplies the result credits; vanishing survival supplies termination.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.FractionalPower

open Program

noncomputable section

private theorem exponent_pos (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    0 < (exponent a b ha hab : ℝ) :=
  div_pos (by exact_mod_cast ha) (by exact_mod_cast lt_of_lt_of_le ha hab)

private theorem hazard_positive (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) (n : ℕ) :
    (0 : ℤ) < (b : ℤ) * ((n : ℤ) + 1) := by
  have hb : (0 : ℤ) < b := by exact_mod_cast lt_of_lt_of_le ha hab
  positivity

private theorem hazard_bounded (a b : ℕ) (_ha : 0 < a) (hab : a ≤ b) (n : ℕ) :
    (a : ℤ) ≤ (b : ℤ) * ((n : ℤ) + 1) := by
  have habz : (a : ℤ) ≤ b := by exact_mod_cast hab
  have hb : (0 : ℤ) ≤ b := by positivity
  nlinarith

private theorem hazard_bias_eq (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) (n : ℕ) :
    RationalCoin.bias (a : ℤ) ((b : ℤ) * ((n : ℤ) + 1)) (by positivity)
      (hazard_positive a b ha hab n) (hazard_bounded a b ha hab n) =
      hazardBias (exponent a b ha hab) n := by
  apply Subtype.ext
  simp only [RationalCoin.bias, hazardBias, exponent, Int.cast_mul, Int.cast_natCast,
    Int.cast_add, Int.cast_one, div_div]

private theorem valid_guard (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    (decide ((a : ℤ) ≤ 0) || decide ((b : ℤ) < a)) = false := by
  have haz : (0 : ℤ) < a := by exact_mod_cast ha
  have habz : (a : ℤ) ≤ b := by exact_mod_cast hab
  simp only [decide_eq_false_iff_not, Bool.or_eq_false_iff, not_le, not_lt]
  exact ⟨haz, habz⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem hazard_spec (E : CoPset) (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) (n : ℕ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.rationalCoin #int (a : ℤ) #int ((b : ℤ) * ((n : ℤ) + 1)))
      (RealCoin.law (hazardBias (exponent a b ha hab) n)) Val.bool := by
  simpa only [hazard_bias_eq a b ha hab n] using
    RationalCoin.rationalCoin_distSpec (GF := GF) E (a : ℤ) ((b : ℤ) * ((n : ℤ) + 1))
      (by positivity) (hazard_positive a b ha hab n) (hazard_bounded a b ha hab n)

private theorem twp_round (E : CoPset) (p : unitInterval) (a b : ℕ)
    (ha : 0 < a) (hab : a ≤ b) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (n : ℕ) (c : ℝ≥0∞)
    (hnext : ⊢ ↯ c -∗ tglWp E
      pl(&(loop coin a b) #int (((n + 1 : ℕ) : ℤ) + 1))
      (fun v : Val rT => iprop(∃ bit : Bool, ⌜v = Val.bool bit⌝ ∗ ↯ (F bit)))) :
    ⊢ ↯ (exitCredit p (exponent a b ha hab) F n +
        continueProb p (exponent a b ha hab) n * c) -∗
      tglWp E pl(&(loop coin a b) #int ((n : ℤ) + 1))
        (fun v : Val rT => iprop(∃ bit : Bool, ⌜v = Val.bool bit⌝ ∗ ↯ (F bit))) := by
  iintro Hcredit
  twp_pures
  isimp only [RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec]
  twp_bind pl(&coin.fst #())
  isimp only [← round_expectation p (exponent a b ha hab) n F c] at Hcredit
  iapply (hcoin.wp (inputCredit (exponent a b ha hab) n F c)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %bit Hcredit
  cases bit
  · isimp only [inputCredit, Bool.false_eq_true, ite_false] at Hcredit
    twp_pure
    twp_pure
    twp_bind pl(&Occil.rationalCoin #int (a : ℤ) #int ((b : ℤ) * ((n : ℤ) + 1)))
    isimp only [← RealCoin.lintegral_law] at Hcredit
    iapply ((hazard_spec E a b ha hab n).wp (hazardCredit F c)
      (measurable_of_countable _) _) $$ Hcredit
    iintro %hazard Hcredit
    cases hazard
    · isimp only [hazardCredit, Bool.false_eq_true, ite_false] at Hcredit
      twp_pure
      twp_pure
      rw [← Nat.cast_add_one]
      have hresume := hnext
      simp only [loop, loopCode] at hresume
      iapply hresume $$ Hcredit
    · isimp only [hazardCredit, ite_true] at Hcredit
      twp_pures
      twp_value
      imodintro
      iexists false
      iframe Hcredit
      itrivial
  · isimp only [inputCredit, ite_true] at Hcredit
    twp_pures
    twp_value
    imodintro
    iexists true
    iframe Hcredit
    itrivial

/-- Finite unfolding and vanishing survival verify the actual reciprocal-hazard loop. -/
theorem twp_loop (E : CoPset) (p : unitInterval) (a b : ℕ)
    (ha : 0 < a) (hab : a ≤ b) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias p a b ha hab) F) -∗
      tglWp E pl(&(loop coin a b) #1)
        (fun v : Val rT => iprop(∃ bit : Bool, ⌜v = Val.bool bit⌝ ∗ ↯ (F bit))) := by
  have hstop : 0 < (p : ℝ) ∨ 0 < (exponent a b ha hab : ℝ) :=
    Or.inr (exponent_pos a b ha hab)
  have h := AbsorbingChain.twp_of_survival (GF := GF) E
    (fun n => pl(&(loop coin a b) #int ((n : ℤ) + 1)))
    (fun v : Val rT => iprop(∃ bit : Bool, ⌜v = Val.bool bit⌝ ∗ ↯ (F bit)))
    (continueProb p (exponent a b ha hab)) (exitCredit p (exponent a b ha hab) F)
    (tailCredit p (exponent a b ha hab) F)
    (tailCredit_succ p (exponent a b ha hab) F)
    (twp_round E p a b ha hab coin hcoin F) 0 (by rfl)
    (absorbs p (exponent a b ha hab) hstop)
  simpa only [tailCredit_zero p (exponent a b ha hab) hstop F,
    Nat.cast_zero, zero_add] using h

/-- The full fractional-power domain, including the infinite-mean endpoint `p=0`. -/
theorem fractionalPower_distSpec (E : CoPset) (p : unitInterval) (a b : ℕ)
    (ha : 0 < a) (hab : a ≤ b) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.fractionalPower &coin.fst #int (a : ℤ) #int (b : ℤ) #())
      (RealCoin.law (bias p a b ha hab)) Val.bool where
  spec F _ := by
    iintro Hcredit
    rw [← source_fst (rT := rT)]
    twp_pures
    rw [valid_guard a b ha hab]
    twp_pure
    twp_pure
    isimp only [RationalCoin.rationalCoin_openRec]
    ieval (change _ ⊢ tglWp E pl(&(loop coin a b) #1) _)
    isimp only [RealCoin.lintegral_law] at Hcredit
    iapply twp_loop E p a b ha hab coin hcoin F $$ Hcredit

end specification

end

end SampLib.FractionalPower
