import SampLib.Templates
import Samplers.Discrete.Combinatorics
import Metrology.Iris.LocalBI

/-! # Exact integer binomial coefficients -/

open ProbLang

namespace SampLib

private def chooseLoop {rT : Type _} (n k : ℕ) : Exp rT := pl%
  rec go i product := if #int (k : ℤ) < i then product else
    go (i + #1) (product * (#int (n : ℤ) - i + #1) / i)

/-- The adjacent binomial identity makes each integer division exact. -/
private theorem choose_step (n i : ℕ) (hi : i < n) :
    (n.choose i : ℤ) * ((n : ℤ) - (i + 1) + 1) / (i + 1) = n.choose (i + 1) := by
  have hmul : (n.choose (i + 1) : ℤ) * (i + 1) = (n.choose i : ℤ) * ((n - i : ℕ) : ℤ) := by
    have h := Nat.choose_succ_right_eq n i
    exact_mod_cast h
  have hsub : ((n - i : ℕ) : ℤ) = (n : ℤ) - i := Nat.cast_sub hi.le
  rw [hsub] at hmul
  have he : (n : ℤ) - (i + 1) + 1 = n - i := by ring
  rw [he, ← hmul, Int.mul_ediv_cancel _ (by omega)]

private theorem choose_done (k : ℕ) : decide ((k : ℤ) < (k + 1 : ℕ)) = true := by
  simp

private theorem choose_continue (i k m : ℕ) (h : i + (m + 1) = k) :
    decide ((k : ℤ) < ((i + 1 : ℕ) : ℤ)) = false := decide_eq_false (by omega)

private theorem choose_guard_le (n k : ℕ) (h : k ≤ n) :
    (false || decide ((n : ℤ) < (k : ℤ))) = false := by
  exact decide_eq_false (by omega)

private theorem choose_guard_gt (n k : ℕ) (h : n < k) :
    (false || decide ((n : ℤ) < (k : ℤ))) = true := by
  exact decide_eq_true (by omega)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_chooseLoop (E : CoPset) (n k i steps : ℕ) (hk : k ≤ n)
    (hi : i + steps = k) :
    ⊢ tglWp E pl(&(chooseLoop n k) #int ((i + 1 : ℕ) : ℤ) #int (n.choose i : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (n.choose k : ℤ)⌝)) := by
  induction steps generalizing i with
  | zero =>
    have he : i = k := by omega
    subst i
    twp_pures
    rw [choose_done]
    twp_pures
    twp_value
    imodintro
    ipureintro
    rfl
  | succ steps ih =>
    twp_pures
    rw [choose_continue i k steps hi]
    iterate 6 twp_pure
    rw [Nat.cast_add_one, choose_step n i (by omega)]
    have h := ih (i + 1) (by omega)
    simp [chooseLoop, Exp.close, Exp.closeRec] at h
    isimp [chooseLoop, Exp.close, Exp.closeRec, Exp.ofVal]
    iapply h

/-- The multiplicative loop computes choose(n,k), including zero when k exceeds n. -/
theorem twp_integerChoose (E : CoPset) (n k : ℕ) :
    ⊢ tglWp E pl(&Occil.DiscreteExtra.choose #int (n : ℤ) #int (k : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (n.choose k : ℤ)⌝)) := by
  by_cases hk : k ≤ n
  · twp_pures
    rw [choose_guard_le n k hk]
    iterate 2 twp_pure
    have h := twp_chooseLoop (rT := rT) (GF := GF) E n k 0 k hk (by simp)
    simp [chooseLoop, Exp.close, Exp.closeRec] at h
    iapply h
  · twp_pures
    rw [choose_guard_gt n k (by omega)]
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp [Nat.choose_eq_zero_of_lt (by omega : n < k)]

end specification

end SampLib
