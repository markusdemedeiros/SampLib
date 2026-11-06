import SampLib.Templates
import SampLib.Weighted.Laws.FenwickLowBit
import Samplers.Weighted.Dynamic

/-! # Computing the least set bit -/

open ProbLang

namespace SampLib.LowBit

private def loop {rT : Type} : Exp rT := pl%
  rec count rest value :=
    if rest % #2 = #1 then value else count (rest / #2) (#2 * value)

private theorem odd_test {rT : Type} [BEq rT] (n : ℕ) :
    ((BaseLit.int ((n : ℤ) % 2) : BaseLit rT) == .int 1) = decide (n % 2 = 1) := by
  change (((n % 2 : ℕ) : ℤ) == ((1 : ℕ) : ℤ)) = decide (n % 2 = 1)
  rw [Bool.beq_eq_decide_eq]
  simp only [Int.natCast_inj]

private theorem even_of_not_odd (n : ℕ) (h : n % 2 ≠ 1) : n % 2 = 0 := by omega

private theorem odd_output (n value : ℕ) (h : n % 2 = 1) :
    value * FenwickMath.lowBit n = value := by
  have he : n = 2 * (n / 2) + 1 := by omega
  rw [he, FenwickMath.lowBit_odd, mul_one]

private theorem even_output (n value : ℕ) (h : n % 2 = 0) :
    (2 * value) * FenwickMath.lowBit (n / 2) = value * FenwickMath.lowBit n := by
  rw [FenwickMath.lowBit_even_quotient h]
  ac_rfl

private theorem positive_guard (n : ℕ) (h : 0 < n) :
    decide ((n : ℤ) ≤ 0) = false := decide_eq_false (by omega)

theorem lowBit_lc {rT : Type} :
    (Occil.WeightedVariants.lowBit : Exp rT).IsLocallyClosed := by is_lc

theorem lowBit_fv {rT : Type} : (Occil.WeightedVariants.lowBit : Exp rT).fv = ∅ := by
  simp [Occil.WeightedVariants.lowBit, Exp.fv]

@[simp] theorem lowBit_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.WeightedVariants.lowBit = Occil.WeightedVariants.lowBit :=
  (Exp.open_lc k e _ lowBit_lc).symm

@[simp] theorem lowBit_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.WeightedVariants.lowBit : Exp rT) =
      Occil.WeightedVariants.lowBit :=
  Exp.closeRec_fresh x _ k (by simp [lowBit_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_loop (E : CoPset) (n value : ℕ) (hn : 0 < n) :
    ⊢ tglWp E pl(&(loop (rT := rT)) #int (n : ℤ) #int (value : ℤ))
      (fun v => iprop(⌜v = Val.int ((value * FenwickMath.lowBit n : ℕ) : ℤ)⌝)) := by
  induction n using Nat.strong_induction_on generalizing value with
  | h n IH =>
    by_cases ho : n % 2 = 1
    · rw [odd_output n value ho]
      twp_pures
      rw [odd_test n]
      simp only [ho, _root_.decide_true]
      twp_pures
      twp_value
      imodintro
      itrivial
    · have he := even_of_not_odd n ho
      have hrec := IH (n / 2) (FenwickMath.quotient_lt hn) (2 * value)
        (FenwickMath.even_quotient_pos hn he)
      rw [even_output n value he] at hrec
      simp [loop, Exp.close, Exp.closeRec] at hrec
      twp_pures
      rw [odd_test n]
      simp only [ho, _root_.decide_false]
      iterate 3 twp_pure
      simp only [Exp.ofVal, Nat.cast_mul]
      iapply hrec

/-- Positive integers return the value of their least significant set bit. -/
theorem twp_lowBit (E : CoPset) (n : ℕ) (hn : 0 < n) :
    ⊢ tglWp E pl(&Occil.WeightedVariants.lowBit #int (n : ℤ))
      (fun v => iprop(⌜v = Val.int (FenwickMath.lowBit n)⌝)) := by
  have hloop := twp_loop (GF := GF) E n 1 hn
  simp [loop, Exp.close, Exp.closeRec] at hloop
  twp_pures
  rw [positive_guard n hn]
  iterate 2 twp_pure
  iapply hloop

end specification

end SampLib.LowBit
