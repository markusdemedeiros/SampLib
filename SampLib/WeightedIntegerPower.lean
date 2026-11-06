import SampLib.Templates
import Samplers.Weighted.Core
import Metrology.Iris.LocalBI

/-! # Integer powers by repeated squaring -/

open ProbLang

namespace SampLib.WeightedIntegerPower

private theorem even_power (x : ℤ) (n : ℕ) (h : n % 2 = 0) :
    x ^ (n / 2) * x ^ (n / 2) = x ^ n := by
  rw [← pow_add]
  congr 1
  omega

private theorem odd_power (x : ℤ) (n : ℕ) (h : n % 2 ≠ 0) :
    x * x ^ (n / 2) * x ^ (n / 2) = x ^ n := by
  rw [mul_assoc, ← pow_add, ← pow_succ']
  congr 1
  omega

private theorem nonzero_test (n : ℕ) (hn : 0 < n) :
    ((n : ℤ) == 0) = false := by simp; omega

private theorem even_test (n : ℕ) (h : n % 2 = 0) :
    ((n : ℤ) % 2 == 0) = true := by
  have hz : (n : ℤ) % 2 = 0 := by omega
  simp [hz]

private theorem odd_test (n : ℕ) (h : n % 2 ≠ 0) :
    ((n : ℤ) % 2 == 0) = false := by
  apply beq_eq_false_iff_ne.mpr
  omega

private theorem int_beq {rT : Type _} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

theorem integerPower_lc {rT : Type _} :
    (Occil.Weighted.integerPower : Exp rT).IsLocallyClosed := by is_lc

theorem integerPower_fv {rT : Type _} :
    (Occil.Weighted.integerPower : Exp rT).fv = ∅ := by
  simp [Occil.Weighted.integerPower, Exp.fv]

@[simp] theorem integerPower_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.Weighted.integerPower = Occil.Weighted.integerPower :=
  (Exp.open_lc k e _ integerPower_lc).symm

@[simp] theorem integerPower_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.Weighted.integerPower : Exp rT) = Occil.Weighted.integerPower :=
  Exp.closeRec_fresh x _ k (by simp [integerPower_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_integerPower (E : CoPset) (x : ℤ) (n : ℕ) :
    ⊢ tglWp E pl(&Occil.Weighted.integerPower #int x #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (x ^ n)⌝)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      twp_pures
      twp_value
      imodintro
      itrivial
    · have hn' : 0 < n := Nat.pos_of_ne_zero hn
      twp_pures
      rw [int_beq, nonzero_test n hn']
      iterate 2 twp_pure
      have hhalf := ih (n / 2) (Nat.div_lt_self hn' (by decide))
      rw [Int.natCast_div] at hhalf
      twp_bind pl(&Occil.Weighted.integerPower #int x #int ((n : ℤ) / 2))
      iapply tglWp_wand
      isplitl []
      · iapply hhalf
      iintro %v %hv
      subst v
      twp_pures
      by_cases he : n % 2 = 0
      · rw [int_beq, even_test n he]
        twp_pures
        twp_value
        imodintro
        ipureintro
        exact congrArg Val.int (even_power x n he)
      · rw [int_beq, odd_test n he]
        twp_pures
        twp_value
        imodintro
        ipureintro
        exact congrArg Val.int (odd_power x n he)

end specification

end SampLib.WeightedIntegerPower
