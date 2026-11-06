import SampLib.Discrete.Laws.IntegerSqrt
import SampLib.Templates
import Samplers.Discrete.Combinatorics

/-! # Deterministic correctness of Occil's integer Newton square root -/

open ProbLang

namespace SampLib.IntegerSqrt

private def loop {rT : Type _} (n : ℕ) : Exp rT := pl%
  rec go x := let next := (x + #int (n : ℤ) / x) / #2;
    if x <= next then x else go next

private theorem halve_cast (n : ℕ) : (n : ℤ) / 2 = ((n / 2 : ℕ) : ℤ) := rfl

private theorem stop_test (n x : ℕ) (h : x ≤ (x + n / x) / 2) :
    decide ((x : ℤ) ≤ (((x + n / x) / 2 : ℕ) : ℤ)) = true :=
  decide_eq_true (by exact_mod_cast h)

private theorem continue_test (n x : ℕ) (h : ¬x ≤ (x + n / x) / 2) :
    decide ((x : ℤ) ≤ (((x + n / x) / 2 : ℕ) : ℤ)) = false :=
  decide_eq_false (by exact_mod_cast h)

private theorem large_test (n : ℕ) (hn : 2 ≤ n) : decide ((n : ℤ) < 2) = false :=
  decide_eq_false (by exact_mod_cast hn.not_gt)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_loop (E : CoPset) (n : ℕ) (hn : 2 ≤ n) (x : ℕ)
    (hbound : Nat.sqrt n ≤ x) :
    ⊢ tglWp E pl(&(loop n) #int (x : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (Nat.sqrt n : ℤ)⌝)) := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
    have hx : 0 < x := (Nat.sqrt_pos.mpr (by omega : 0 < n)).trans_le hbound
    by_cases hstop : x ≤ (x + n / x) / 2
    · have heq : x = Nat.sqrt n := (newton_terminal n x hx hstop).antisymm hbound
      twp_pures
      rw [← Int.natCast_ediv, ← Nat.cast_add, halve_cast, stop_test n x hstop]
      twp_pures
      twp_value
      imodintro
      ipureintro
      apply Val.ext
      simp [heq]
    · have hnext := newton_lower_bound n x hx
      have hsmaller : (x + n / x) / 2 < x := by omega
      twp_pures
      rw [← Int.natCast_ediv, ← Nat.cast_add, halve_cast, continue_test n x hstop]
      twp_pure
      have h := ih ((x + n / x) / 2) hsmaller hnext
      simp [loop, Exp.close, Exp.closeRec] at h
      isimp [loop, Exp.close, Exp.closeRec, Exp.ofVal]
      iapply h

/-- The supplied Newton program computes the floor square root for every natural input. -/
theorem twp_integerSqrt (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&Occil.DiscreteExtra.integerSqrt #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (Nat.sqrt n : ℤ)⌝)) := by
  by_cases hn : n < 2
  · interval_cases n <;> twp_pures <;> twp_value <;> imodintro <;> ipureintro <;> norm_num
  · twp_pures
    rw [large_test n (by omega)]
    iterate 2 twp_pure
    have h := twp_loop (rT := rT) (GF := GF) E n (by omega) n (Nat.sqrt_le_self n)
    simp only [loop] at h
    exact h

end specification

end SampLib.IntegerSqrt
