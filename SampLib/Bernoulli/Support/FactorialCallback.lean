import SampLib.Templates

/-! # The descending factorial callback used in trigonometric coefficient terms -/

open ProbLang

namespace SampLib.FactorialCallback

def factorial {rT : Type} : Exp rT := pl%
  rec product n := if n <= #1 then #1 else n * product (n - #1)

/-- Closed recursive value obtained when the source's local factorial is evaluated. -/
def factorialCode {rT : Type} : Exp rT :=
  .fix (.lam (.cond (.binop .le (.bvar 0) (.lit (.int 1))) (.lit (.int 1))
    (.binop .mult (.bvar 0)
      (.app (.bvar 1) (.binop .minus (.bvar 0) (.lit (.int 1)))))))

theorem factorial_eq_code {rT : Type} : (factorial : Exp rT) = factorialCode := by
  simp [factorial, factorialCode, Exp.close, Exp.closeRec, Var.internal.injEq]

theorem factorial_fv {rT : Type} : (factorial : Exp rT).fv = ∅ := by
  simp [factorial, Exp.fv]

@[simp] theorem factorial_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e factorial = factorial :=
  (Exp.open_lc k e _ (by is_lc)).symm

@[simp] theorem factorial_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (factorial : Exp rT) = factorial :=
  Exp.closeRec_fresh x _ k (by simp [factorial_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Factorial calculation terminates for each nonnegative integer argument. -/
theorem twp_factorial (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&factorial #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int n.factorial⌝)) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    twp_pures
    twp_value
    imodintro
    ipureintro
    rfl
  | one =>
    twp_pures
    twp_value
    imodintro
    ipureintro
    rfl
  | more n _ IH =>
    have hn : ¬((n + 2 : ℕ) : ℤ) ≤ 1 := by omega
    iterate 4 twp_pure
    twp_pure
    rw [show ((n + 2 : ℕ) : ℤ) - 1 = ((n + 1 : ℕ) : ℤ) by omega]
    twp_bind pl(&factorial #int ((n + 1 : ℕ) : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply IH
    iintro %v %hv
    subst v
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp [Nat.factorial_succ, add_assoc]

end specification

end SampLib.FactorialCallback
