import SampLib.Templates
import Samplers.Bernoulli.Arithmetic

/-! # The rising-product binomial coefficient used by coin factories -/

open ProbLang

namespace SampLib.FactoryChoose

private def loop {rT : Type} (n k : ℕ) : Exp rT := pl%
  rec product i value := if #int (k : ℤ) < i then value else
    product (i + #1) (value * (#int (n : ℤ) - #int (k : ℤ) + i) / i)

/-- The rising numerator maintains choose(n-k+i,i) with exact integer division. -/
private theorem step (n k i : ℕ) (hk : k ≤ n) :
    ((n - k + i).choose i : ℤ) * ((n : ℤ) - k + (i + 1)) / (i + 1) =
      (n - k + (i + 1)).choose (i + 1) := by
  have h : (((n - k + i + 1).choose (i + 1) : ℕ) : ℤ) * (i + 1) =
      ((n - k + i).choose i : ℤ) * ((n - k + i + 1 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq (n - k + i) i).symm.trans (mul_comm _ _)
  have hc : ((n - k + i + 1 : ℕ) : ℤ) = (n : ℤ) - k + (i + 1) := by
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub hk, Nat.cast_one]
    ring
  rw [hc] at h
  rw [← h, Int.mul_ediv_cancel _ (by omega)]
  simp only [Nat.add_assoc]

private theorem done (k : ℕ) : decide ((k : ℤ) < ((k + 1 : ℕ) : ℤ)) = true := by simp

private theorem continuing (i k steps : ℕ) (h : i + (steps + 1) = k) :
    decide ((k : ℤ) < ((i + 1 : ℕ) : ℤ)) = false := decide_eq_false (by omega)

private theorem guard_le (n k : ℕ) (h : k ≤ n) :
    (false || decide ((n : ℤ) < k)) = false := decide_eq_false (by omega)

private theorem guard_gt (n k : ℕ) (h : n < k) :
    (false || decide ((n : ℤ) < k)) = true := decide_eq_true (by omega)

theorem choose_lc {rT : Type} : (Occil.FactoryExtra.choose : Exp rT).IsLocallyClosed := by
  is_lc

theorem choose_fv {rT : Type} : (Occil.FactoryExtra.choose : Exp rT).fv = ∅ := by
  simp [Occil.FactoryExtra.choose, Exp.fv]

@[simp] theorem choose_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.FactoryExtra.choose = Occil.FactoryExtra.choose :=
  (Exp.open_lc k e _ choose_lc).symm

@[simp] theorem choose_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.FactoryExtra.choose : Exp rT) = Occil.FactoryExtra.choose :=
  Exp.closeRec_fresh x _ k (by simp [choose_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_loop (E : CoPset) (n k i steps : ℕ) (hk : k ≤ n)
    (hi : i + steps = k) :
    ⊢ tglWp E pl(&(loop n k) #int ((i + 1 : ℕ) : ℤ) #int ((n - k + i).choose i : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (n.choose k : ℤ)⌝)) := by
  induction steps generalizing i with
  | zero =>
    have he : i = k := by simpa using hi
    subst i
    twp_pures
    rw [done]
    twp_pures
    twp_value
    imodintro
    ipureintro
    apply Val.ext
    simp [Nat.sub_add_cancel hk]
  | succ steps IH =>
    twp_pures
    rw [continuing i k steps hi]
    iterate 6 twp_pure
    rw [Nat.cast_add_one, step n k i hk]
    have h := IH (i + 1) (by simpa only [Nat.add_assoc, Nat.add_comm 1 steps] using hi)
    simp [loop, Exp.close, Exp.closeRec] at h
    isimp [loop, Exp.close, Exp.closeRec, Exp.ofVal]
    iapply h

/-- The actual factory helper computes choose(n,k), including zero for k>n. -/
theorem twp_choose (E : CoPset) (n k : ℕ) :
    ⊢ tglWp E pl(&Occil.FactoryExtra.choose #int (n : ℤ) #int (k : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (n.choose k : ℤ)⌝)) := by
  by_cases hk : k ≤ n
  · twp_pures
    rw [guard_le n k hk]
    iterate 2 twp_pure
    have h := twp_loop (rT := rT) (GF := GF) E n k 0 k hk (by simp)
    simp [loop, Exp.close, Exp.closeRec] at h
    iapply h
  · twp_pures
    rw [guard_gt n k (Nat.lt_of_not_ge hk)]
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)]

end specification

end SampLib.FactoryChoose
