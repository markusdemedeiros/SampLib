import SampLib.Templates
import SampLib.Weighted.Laws.PowerOfTwoCeiling
import Samplers.Weighted.Core
import Metrology.Iris.LocalBI

/-! # Computing the least enclosing binary word width

The doubling loop returns `PowerOfTwoCeiling.width n`.
-/

open ProbLang

namespace SampLib.PowerOfTwoCeiling

theorem powerOfTwoCeiling_lc {rT : Type _} :
    (Occil.Weighted.powerOfTwoCeiling : Exp rT).IsLocallyClosed := by is_lc

theorem powerOfTwoCeiling_fv {rT : Type _} :
    (Occil.Weighted.powerOfTwoCeiling : Exp rT).fv = ∅ := by
  simp [Occil.Weighted.powerOfTwoCeiling, Exp.fv]

@[simp] theorem powerOfTwoCeiling_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.Weighted.powerOfTwoCeiling = Occil.Weighted.powerOfTwoCeiling :=
  (Exp.open_lc k e _ powerOfTwoCeiling_lc).symm

@[simp] theorem powerOfTwoCeiling_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.Weighted.powerOfTwoCeiling : Exp rT) =
      Occil.Weighted.powerOfTwoCeiling :=
  Exp.closeRec_fresh x _ k (by simp [powerOfTwoCeiling_fv])

private def loop {rT : Type _} (n : ℕ) : Exp rT := pl%
  rec double value := if #int (n : ℤ) <= value then value else double (value * #2)

private theorem power_test (n j : ℕ) :
    decide ((n : ℤ) ≤ (2 : ℤ) ^ j) = decide (Nat.clog 2 n ≤ j) := by
  congr 1
  rw [Nat.clog_le_iff_le_pow (by decide)]
  exact_mod_cast (rfl : (n ≤ 2 ^ j) = (n ≤ 2 ^ j))

private theorem power_cast (j : ℕ) :
    (2 : ℤ) ^ j = ((2 ^ j : ℕ) : ℤ) := by norm_cast

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_loop (E : CoPset) (n j fuel : ℕ)
    (h : j + fuel = Nat.clog 2 n) :
    ⊢ tglWp E pl(&(loop n) #int ((2 : ℤ) ^ j))
      (fun v : Val rT => iprop(⌜v = Val.int (width n : ℤ)⌝)) := by
  induction fuel generalizing j with
  | zero =>
    have hj : j = Nat.clog 2 n := by omega
    twp_pures
    rw [power_test, hj, decide_eq_true (Nat.le_refl _)]
    twp_pures
    twp_value
    imodintro
    ipureintro
    subst j
    exact congrArg Val.int (power_cast _)
  | succ fuel ih =>
    have hj : j < Nat.clog 2 n := by omega
    twp_pures
    rw [power_test, decide_eq_false (Nat.not_le.mpr hj)]
    iterate 2 twp_pure
    rw [← pow_succ]
    have hrec := ih (j + 1) (by omega)
    simp [loop, Exp.close, Exp.closeRec] at hrec
    iapply hrec

/-- Pure preprocessing computes the exact enclosing power of two. -/
theorem twp_powerOfTwoCeiling (E : CoPset) (n : ℕ) (hn : 0 < n) :
    ⊢ tglWp E pl(&Occil.Weighted.powerOfTwoCeiling #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (width n : ℤ)⌝)) := by
  have hloop := twp_loop (rT := rT) (GF := GF) E n 0 (Nat.clog 2 n) (by simp)
  simp [loop, Exp.close, Exp.closeRec] at hloop
  twp_pures
  rw [show decide ((n : ℤ) ≤ 0) = false by simp; omega]
  iterate 2 twp_pure
  iapply hloop

end specification

end SampLib.PowerOfTwoCeiling
