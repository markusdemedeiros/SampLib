import SampLib.Common.FractionalPowerCore
import SampLib.Bernoulli.CoinProduct
import SampLib.Bernoulli.Syntax.TwoCoinPower

/-! # The two-coin reciprocal-hazard power factory -/

open ProbLang
open scoped ENNReal

namespace SampLib.TwoCoinPower

open Program

noncomputable section

abbrev bias := FractionalPower.powerBias

def exponentCredit (n : ℕ) (F : Bool → ℝ≥0∞) (c : ℝ≥0∞) : Bool → ℝ≥0∞ :=
  CoinProduct.firstCredit (FractionalPower.hazardBias 1 n) (FractionalPower.hazardCredit F c)

def firstCredit (q : unitInterval) (n : ℕ) (F : Bool → ℝ≥0∞)
    (c : ℝ≥0∞) (bit : Bool) : ℝ≥0∞ :=
  if bit then F true else RealCoin.credit q (exponentCredit n F c)

/-- Testing the exponent coin and `1/(n+1)` coin is a hazard of `q/(n+1)`. -/
private theorem exponent_expectation (q : unitInterval) (n : ℕ)
    (F : Bool → ℝ≥0∞) (c : ℝ≥0∞) :
    RealCoin.credit q (exponentCredit n F c) =
      RealCoin.credit (FractionalPower.hazardBias q n) (FractionalPower.hazardCredit F c) := by
  have hb : q * FractionalPower.hazardBias 1 n = FractionalPower.hazardBias q n := by
    apply Subtype.ext
    simp [FractionalPower.hazardBias, div_eq_mul_inv]
  simpa only [exponentCredit, RealCoin.lintegral_law, CoinProduct.law, hb] using
    CoinProduct.expectation_preservation q (FractionalPower.hazardBias 1 n)
      (FractionalPower.hazardCredit F c)

/-- First-round conditioning is the same power-law recurrence for arbitrary credits. -/
theorem round_expectation (p q : unitInterval) (n : ℕ) (F : Bool → ℝ≥0∞) (c : ℝ≥0∞) :
    ∫⁻ bit, firstCredit q n F c bit ∂RealCoin.law p =
      FractionalPower.exitCredit p q F n + FractionalPower.continueProb p q n * c := by
  have hfirst : firstCredit q n F c = FractionalPower.inputCredit q n F c := by
    funext bit
    cases bit <;> simp only [firstCredit, FractionalPower.inputCredit,
      Bool.false_eq_true, ite_false, ite_true, exponent_expectation]
  rw [hfirst, FractionalPower.round_expectation]


private theorem gate_bias_eq (n : ℕ) :
    RationalCoin.bias 1 ((n : ℤ) + 1) (by positivity) (by positivity) (by omega) =
      FractionalPower.hazardBias 1 n := by
  apply Subtype.ext
  simp [RationalCoin.bias, FractionalPower.hazardBias]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem gate_spec (E : CoPset) (n : ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.rationalCoin #1 #int ((n : ℤ) + 1))
      (RealCoin.law (FractionalPower.hazardBias 1 n)) Val.bool := by
  simpa only [gate_bias_eq n] using
    RationalCoin.rationalCoin_distSpec (GF := GF) E 1 ((n : ℤ) + 1)
      (by positivity) (by positivity) (by omega)

private theorem twp_round (E : CoPset) (p q : unitInterval) (base exponent : Val rT)
    (hbase : IsDistSpec (GF := GF) E pl(&base.fst #()) (RealCoin.law p) Val.bool)
    (hexponent : IsDistSpec (GF := GF) E pl(&exponent.fst #()) (RealCoin.law q) Val.bool)
    (F : Bool → ℝ≥0∞) (n : ℕ) (c : ℝ≥0∞)
    (hnext : ⊢ ↯ c -∗ tglWp E pl(&(loop base exponent) #int (((n + 1 : ℕ) : ℤ) + 1))
      (fun v : Val rT => iprop(∃ (bit : Bool), ⌜v = Val.bool bit⌝ ∗ ↯ (F bit)))) :
    ⊢ ↯ (FractionalPower.exitCredit p q F n + FractionalPower.continueProb p q n * c) -∗
      tglWp E pl(&(loop base exponent) #int ((n : ℤ) + 1))
        (fun v : Val rT => iprop(∃ (bit : Bool), ⌜v = Val.bool bit⌝ ∗ ↯ (F bit))) := by
  iintro Hcredit
  twp_pures
  isimp only [RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec]
  twp_bind pl(&base.fst #())
  isimp only [← round_expectation p q n F c] at Hcredit
  iapply (hbase.wp (firstCredit q n F c) (measurable_of_countable _) _) $$ Hcredit
  iintro %bit Hcredit
  cases bit
  · isimp only [firstCredit, Bool.false_eq_true, ite_false,
      ← RealCoin.lintegral_law] at Hcredit
    twp_pure
    twp_bind pl(&exponent.fst #())
    iapply (hexponent.wp (exponentCredit n F c) (measurable_of_countable _) _) $$ Hcredit
    iintro %select Hcredit
    cases select
    · isimp only [exponentCredit, CoinProduct.firstCredit,
        FractionalPower.hazardCredit, Bool.false_eq_true, ite_false] at Hcredit
      twp_pure
      twp_pure
      rw [← Nat.cast_add_one]
      have hresume := hnext
      simp only [loop, loopCode] at hresume
      iapply hresume $$ Hcredit
    · isimp only [exponentCredit, CoinProduct.firstCredit, ite_true] at Hcredit
      twp_pure
      twp_bind pl(&Occil.rationalCoin #1 #int ((n : ℤ) + 1))
      iapply ((gate_spec E n).wp (FractionalPower.hazardCredit F c)
        (measurable_of_countable _) _) $$ Hcredit
      iintro %gate Hcredit
      cases gate
      · isimp only [FractionalPower.hazardCredit, Bool.false_eq_true, ite_false] at Hcredit
        twp_pure
        twp_pure
        rw [← Nat.cast_add_one]
        have hresume := hnext
        simp only [loop, loopCode] at hresume
        iapply hresume $$ Hcredit
      · isimp only [FractionalPower.hazardCredit, ite_true] at Hcredit
        twp_pures
        twp_value
        imodintro
        iexists false
        iframe Hcredit
        itrivial
  · isimp only [firstCredit, ite_true] at Hcredit
    twp_pures
    twp_value
    imodintro
    iexists true
    iframe Hcredit
    itrivial

private theorem twp_loop (E : CoPset) (p q : unitInterval)
    (hstop : 0 < (p : ℝ) ∨ 0 < (q : ℝ)) (base exponent : Val rT)
    (hbase : IsDistSpec (GF := GF) E pl(&base.fst #()) (RealCoin.law p) Val.bool)
    (hexponent : IsDistSpec (GF := GF) E pl(&exponent.fst #()) (RealCoin.law q) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias p q) F) -∗ tglWp E pl(&(loop base exponent) #1)
      (fun v : Val rT => iprop(∃ (bit : Bool), ⌜v = Val.bool bit⌝ ∗ ↯ (F bit))) := by
  have h := AbsorbingChain.twp_of_survival (GF := GF) E
    (fun n => pl(&(loop base exponent) #int ((n : ℤ) + 1)))
    (fun v : Val rT => iprop(∃ (bit : Bool), ⌜v = Val.bool bit⌝ ∗ ↯ (F bit)))
    (FractionalPower.continueProb p q) (FractionalPower.exitCredit p q F)
    (FractionalPower.tailCredit p q F) (FractionalPower.tailCredit_succ p q F)
    (twp_round E p q base exponent hbase hexponent F) 0 (by rfl)
    (FractionalPower.absorbs p q hstop)
  simpa only [FractionalPower.tailCredit_zero p q hstop F, Nat.cast_zero, zero_add] using h

/-- The full terminating domain excludes exactly the pair of zero input biases. -/
theorem twoCoinPower_distSpec (E : CoPset) (p q : unitInterval)
    (hstop : 0 < (p : ℝ) ∨ 0 < (q : ℝ)) (base exponent : Val rT)
    (hbase : IsDistSpec (GF := GF) E pl(&base.fst #()) (RealCoin.law p) Val.bool)
    (hexponent : IsDistSpec (GF := GF) E pl(&exponent.fst #()) (RealCoin.law q) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.twoCoinPower &base.fst &exponent.fst #())
      (RealCoin.law (bias p q)) Val.bool where
  spec F _ := by
    iintro Hcredit
    rw [← source_fst (rT := rT)]
    iterate 4 twp_pure
    isimp only [RationalCoin.rationalCoin_openRec]
    ieval (
      change _ ⊢ tglWp E pl(&(loop base exponent) #1)
        (fun v : Val rT => iprop(∃ (bit : Bool), ⌜v = Val.bool bit⌝ ∗ ↯ (F bit))))
    isimp only [RealCoin.lintegral_law] at Hcredit
    have hloop := twp_loop E p q hstop base exponent hbase hexponent F
    iapply hloop $$ Hcredit

end specification

end

end SampLib.TwoCoinPower
