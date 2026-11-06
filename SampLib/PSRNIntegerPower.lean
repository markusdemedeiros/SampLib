import SampLib.Templates
import SampLib.Syntax.ClosedExp
import Samplers.PSRN.Core

/-! # Exact powers in interval denominators -/

open ProbLang

namespace SampLib.PSRNIntegerPower

instance integerPower_closed {rT : Type} :
    ClosedExp (Occil.PSRN.integerPower : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.PSRN.integerPower, Exp.fv]

private theorem square_half (x : ℤ) (n : ℕ) (h : n % 2 = 0) :
    x ^ (n / 2) * x ^ (n / 2) = x ^ n := by
  rw [← pow_add]
  congr 1
  omega

private theorem odd_half (x : ℤ) (n : ℕ) (h : n % 2 ≠ 0) :
    x * x ^ (n / 2) * x ^ (n / 2) = x ^ n := by
  rw [mul_assoc, ← pow_add, ← pow_succ']
  congr 1
  omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The binary recursion computes integer powers without consuming credits. -/
theorem twp_integerPower (E : CoPset) (x : ℤ) (n : ℕ) :
    ⊢ tglWp E pl(&Occil.PSRN.integerPower #int x #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (x ^ n)⌝)) := by
  induction n using Nat.strong_induction_on with
  | h n IH =>
    by_cases hn : n = 0
    · subst n
      twp_pures
      twp_value
      imodintro
      ipureintro
      simp
    · have hn' : 0 < n := Nat.pos_of_ne_zero hn
      twp_pures
      have hzero : ((BaseLit.int (n : ℤ) : BaseLit rT) == .int 0) = false := by
        change ((n : ℤ) == 0) = false
        simp [hn]
      rw [hzero]
      iterate 2 twp_pure
      have hrec := IH (n / 2) (Nat.div_lt_self hn' (by decide))
      rw [Int.natCast_div] at hrec
      twp_bind pl(&Occil.PSRN.integerPower #int x #int ((n : ℤ) / 2))
      iapply tglWp_wand
      isplitl []
      · iapply hrec
      iintro %v %hv
      subst v
      by_cases heven : n % 2 = 0
      · have heven' : (n : ℤ) % 2 = 0 := by exact_mod_cast heven
        twp_pures
        isimp only [heven', beq_self_eq_true]
        twp_pures
        twp_value
        imodintro
        ipureintro
        exact congrArg Val.int (square_half x n heven)
      · have hodd : (n : ℤ) % 2 ≠ 0 := by exact_mod_cast heven
        have htest : ((BaseLit.int ((n : ℤ) % 2) : BaseLit rT) == .int 0) = false := by
          change ((n : ℤ) % 2 == 0) = false
          simp [hodd]
        twp_pures
        rw [htest]
        twp_pures
        twp_value
        imodintro
        ipureintro
        exact congrArg Val.int (odd_half x n heven)

end specification

end SampLib.PSRNIntegerPower
