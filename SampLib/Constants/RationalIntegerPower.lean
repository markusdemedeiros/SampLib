import SampLib.Continuous.IterateCoin
import SampLib.Uniform.RationalCoin
import Samplers.Constants.Special

/-! # Integer powers of a rational coin

Finite induction uses the all-successes expectation recurrence. No termination slack is needed.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.RationalIntegerPower

noncomputable section

abbrev bias (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b) (n : ℕ) :=
  IterateCoin.bias (RationalCoin.bias a b ha hb hab) n

@[simp] theorem bias_coe (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b) (n : ℕ) :
    (bias a b ha hb hab n : ℝ) = ((a : ℝ) / b) ^ n := rfl

@[pl_fold] private def loop {rT : Type} (a b : ℤ) : Exp rT :=
  .fix (.lam (.cond (.binop .eq (.bvar 0) (.lit (.int 0))) (.lit (.bool true))
    (.cond (.app (.app Occil.rationalCoin (.lit (.int a))) (.lit (.int b)))
      (.app (.bvar 1) (.binop .minus (.bvar 0) (.lit (.int 1)))) (.lit (.bool false)))))

private theorem credit_zero (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b)
    (F : Bool → ℝ≥0∞) : RealCoin.credit (bias a b ha hb hab 0) F = F true :=
  IterateCoin.credit_zero _ F

theorem expectation (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b)
    (n : ℕ) (F : Bool → ℝ≥0∞) :
    (∫⁻ r, IterateCoin.continuation (RationalCoin.bias a b ha hb hab) n F r
      ∂RealCoin.law (RationalCoin.bias a b ha hb hab)) =
        RealCoin.credit (bias a b ha hb hab (n + 1)) F :=
  IterateCoin.expectation _ n F

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_loop (E : CoPset) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b)
    (n : ℕ) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias a b ha hb hab n) F) -∗
      tglWp E pl(&(loop a b : Exp rT) #int (n : ℤ))
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
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
    iterate 4 twp_pure
    simp only [RationalCoin.rationalCoin_openRec]
    twp_bind pl(&Occil.rationalCoin #int a #int b)
    isimp only [← expectation a b ha hb hab n F] at Hcredit
    iapply ((RationalCoin.rationalCoin_distSpec E a b ha hb hab).wp
      (IterateCoin.continuation (RationalCoin.bias a b ha hb hab) n F)
      (measurable_of_countable _) _) $$ Hcredit
    iintro %r Hcredit
    cases r
    · twp_pures
      twp_value
      imodintro
      iexists false
      isimp only [IterateCoin.continuation, Bool.false_eq_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pure
      twp_pure
      rw [Nat.cast_add_one, add_sub_cancel_right]
      isimp only [IterateCoin.continuation, ite_true, IterateCoin.credit] at Hcredit
      twp_bind pl(&(loop a b : Exp rT) #int (n : ℤ))
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply IH $$ Hcredit

/-- All nonnegative integer powers, including the zeroth power at base zero. -/
theorem rationalIntegerPower_distSpec (E : CoPset) (a b : ℤ)
    (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b) (n : ℕ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.Constants.rationalIntegerPower #int a #int b #int (n : ℤ) #())
      (RealCoin.law (bias a b ha hb hab n)) Val.bool where
  spec F _ := by
    iintro Hcredit
    iterate 7 twp_pure
    isimp only [RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec]
    isimp only [RealCoin.lintegral_law] at Hcredit
    have hloop := twp_loop (rT := rT) (GF := GF) E a b ha hb hab n F
    simp only [loop] at hloop
    iapply hloop $$ Hcredit

end specification

end

end SampLib.RationalIntegerPower
