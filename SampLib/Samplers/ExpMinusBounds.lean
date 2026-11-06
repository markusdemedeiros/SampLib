import SampLib.Distributions.ExponentialBoundsKernel
import Samplers.Constants.Exponential
import SampLib.Syntax.ClosedExp
import Metrology.Iris.LocalBI

/-! # The concrete integer Taylor gateway for `exp(-x/y)` -/

open ProbLang

namespace SampLib.ExponentialEnclosure

-- Parameters are inserted only after all structural binders are finalized.
private def accumulateCode {rT : Type} (x y m : ℕ → Exp rT) : Exp rT :=
  let bind (rhs body : Exp rT) := Exp.app (.lam body) rhs
  let output := Exp.cond (.binop .lt (.bvar 2) (.lit (.int 0)))
    (.pair (.binop .plus (.bvar 1) (.bvar 2)) (.pair (.bvar 1) (.bvar 0)))
    (.pair (.bvar 1) (.pair (.binop .plus (.bvar 1) (.bvar 2)) (.bvar 0)))
  let retry := Exp.app (.app (.app (.app (.bvar 9) (.bvar 4)) (.bvar 2))
    (.binop .plus (.bvar 1) (.bvar 2))) (.bvar 0)
  let body := Exp.cond (.binop .eq (.bvar 8) (m 10)) output retry
  let body := bind (.binop .mult (.bvar 4) (.bvar 2)) body
  let body := bind (.binop .mult (.bvar 4) (.bvar 1)) body
  let body := bind (.unop .minus (.binop .mult (.bvar 4) (x 7))) body
  let body := bind (.binop .mult (y 6) (.bvar 0)) body
  let body := bind (.binop .plus (.bvar 3) (.lit (.int 1))) body
  .fix (.lam (.lam (.lam (.lam body))))

@[pl_fold] private def accumulate {rT : Type} (x y m : ℕ) : Exp rT :=
  accumulateCode (fun _ => .lit (.int x)) (fun _ => .lit (.int y)) (fun _ => .lit (.int m))

private def sourceCode {rT : Type} : Exp rT :=
  let guard := Exp.binop .or (.binop .or (.binop .lt (.bvar 2) (.lit (.int 0)))
    (.binop .le (.bvar 1) (.lit (.int 0)))) (.binop .lt (.bvar 0) (.lit (.int 0)))
  let last := Exp.binop .plus (.binop .plus (.binop .div (.bvar 2) (.bvar 1))
    (.binop .mult (.lit (.int 2)) (.bvar 0))) (.lit (.int 1))
  let call := Exp.app (.app (.app (.app (.bvar 0) (.lit (.int 0))) (.lit (.int 1)))
    (.lit (.int 1))) (.lit (.int 1))
  let loop := accumulateCode (fun k => .bvar (k + 3)) (fun k => .bvar (k + 2))
    (fun k => .bvar k)
  .lam (.lam (.lam (.cond guard .fail (.app (.lam (.app (.lam call) loop)) last))))

private theorem source_eq {rT : Type} :
    (Occil.Constants.expMinusBounds : Exp rT) = sourceCode := by
  kernel_rfl

private instance accumulate_closed {rT : Type} (x y m : ℕ) :
    ClosedExp (accumulate (rT := rT) x y m) where
  lc := by is_lc
  fv := by simp [accumulate, accumulateCode, Exp.fv]

private theorem power_step (x k : ℕ) :
    -((-(x : ℤ)) ^ k * (x : ℤ)) = (-(x : ℤ)) ^ (k + 1) := by
  rw [pow_succ]
  ring

private theorem natural_test {rT : Type} [BEq rT] (a b : ℕ) :
    ((BaseLit.int (a : ℤ) : BaseLit rT) == .int (b : ℤ)) = decide (a = b) := by
  change decide ((a : ℤ) = (b : ℤ)) = decide (a = b)
  exact decide_eq_decide.mpr (by omega)

private theorem valid_guard (y : ℕ) (hy : 0 < y) :
    ((false || decide ((y : ℤ) ≤ 0)) || false) = false := by
  simp [hy.ne']

private theorem last_cast (x y n : ℕ) :
    (x : ℤ) / y + 2 * n + 1 = (last x y n : ℤ) := by
  simp [last, Nat.cast_add, Nat.cast_mul]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

private theorem twp_accumulate (E : CoPset) (x y m k : ℕ) (hk : k ≤ m) :
    ⊢ tglWp E pl(&(accumulate x y m) #int (k : ℤ) #int ((-(x : ℤ)) ^ k)
      #int (numerator x y k) #int (denominator y k : ℤ))
      (fun v : Val rT => iprop(⌜v = RealEnclosure.encodeTriple
        (lower x y m, (upper x y m, (denominator y (m + 1) : ℤ)))⌝)) := by
  refine Nat.decreasingInduction ?_ ?_ hk
  · intro k hk IH
    iterate 17 twp_pure
    rw [natural_test k m, decide_eq_false (Nat.ne_of_lt hk)]
    iterate 2 twp_pure
    have h := IH
    simp only [numerator, denominator, Nat.factorial_succ, Nat.cast_add,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_one, pow_succ, neg_mul,
      mul_comm, mul_left_comm, mul_assoc, Exp.ofVal] at h ⊢
    exact h
  · iterate 17 twp_pure
    rw [natural_test m m, decide_eq_true rfl]
    twp_pures
    rw [power_step]
    by_cases hδ : (-(x : ℤ)) ^ (m + 1) < 0
    · rw [decide_eq_true hδ]
      twp_pures
      twp_value
      imodintro
      ipureintro
      have hp : power x m < 0 := hδ
      rw [lower, upper, ite_eq_left hp, ite_eq_left hp]
      apply Val.ext
      simp [RealEnclosure.encodeTriple, power, middle, denominator, Nat.factorial_succ,
        pow_succ, Exp.ofVal, mul_comm, mul_left_comm, mul_assoc]
    · rw [decide_eq_false hδ]
      twp_pures
      twp_value
      imodintro
      ipureintro
      have hp : ¬power x m < 0 := hδ
      rw [lower, upper, ite_eq_right hp, ite_eq_right hp]
      apply Val.ext
      simp [RealEnclosure.encodeTriple, power, middle, denominator, Nat.factorial_succ,
        pow_succ, Exp.ofVal, mul_comm, mul_left_comm, mul_assoc]

/-- The actual signed integer oracle returns the exact Taylor enclosure at every index. -/
theorem twp_expMinusBounds (E : CoPset) (x y : ℕ) (hy : 0 < y) (n : ℕ) :
    ⊢ tglWp E pl(&Occil.Constants.expMinusBounds #int (x : ℤ) #int (y : ℤ) #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = RealEnclosure.encodeInterval (interval x y hy n)⌝)) := by
  rw [source_eq]
  simp only [sourceCode, accumulateCode]
  iterate 3 twp_pure
  twp_pures
  rw [valid_guard y hy]
  iterate 7 twp_pure
  rw [last_cast]
  have h := twp_accumulate (rT := rT) (GF := GF) E x y (last x y n) 0 (Nat.zero_le _)
  simp only [numerator, denominator, Nat.factorial_zero, Nat.cast_one,
    Nat.cast_zero, pow_zero, mul_one] at h
  exact h

end specification

end SampLib.ExponentialEnclosure
