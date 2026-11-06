import SampLib.ArrayOwnership

/-! # Read-only searches through alias preprocessing work arrays -/

open ProbLang

namespace SampLib.WalkerFind

def eligible (below : Bool) (total value : ℕ) : Prop :=
  if below then value < total else total < value

def before {n : ℕ} (work : Fin n → ℕ) (below : Bool) (total start : ℕ) : Prop :=
  ∀ i : Fin n, i.val < start → ¬ eligible below total (work i)

def result {n : ℕ} (work : Fin n → ℕ) (below : Bool) (total : ℕ) (r : ℤ) : Prop :=
  (r = -1 ∧ ∀ i : Fin n, ¬ eligible below total (work i)) ∨
    ∃ i : Fin n, r = (i.val : ℤ) ∧ eligible below total (work i)

/-- The source scans by index and returns -1 only when no eligible column exists. -/
def find {rT : Type} (l : Loc) (n total : ℕ) : Exp rT := pl%
  rec scan i low := if i = #int (n : ℤ) then #(-1) else
    let w := !(#loc l +ₗ i);
    if low then if w < #int (total : ℤ) then i else scan (i + #1) low
    else if #int (total : ℤ) < w then i else scan (i + #1) low

theorem find_lc {rT : Type} (l : Loc) (n total : ℕ) :
    (find (rT := rT) l n total).IsLocallyClosed := by is_lc

theorem find_fv {rT : Type} (l : Loc) (n total : ℕ) :
    (find (rT := rT) l n total).fv = ∅ := by simp [find, Exp.fv]

@[simp] theorem find_openRec {rT : Type} (l : Loc) (n total k : ℕ) (e : Exp rT) :
    Exp.openRec k e (find l n total) = find l n total :=
  (Exp.open_lc k e _ (find_lc l n total)).symm

@[simp] theorem find_closeRec {rT : Type} (l : Loc) (n total k : ℕ) (x : Var) :
    Exp.closeRec k x (find (rT := rT) l n total) = find l n total :=
  Exp.closeRec_fresh x _ k (by simp [find_fv])

theorem before_zero {n : ℕ} (work : Fin n → ℕ) (below : Bool) (total : ℕ) :
    before work below total 0 := by
  intro i hi
  exact (Nat.not_lt_zero i.val hi).elim

theorem before_end {n : ℕ} {work : Fin n → ℕ} {below : Bool} {total : ℕ}
    (h : before work below total n) : ∀ i, ¬ eligible below total (work i) :=
  fun i => h i i.isLt

theorem before_step {n : ℕ} {work : Fin n → ℕ} {below : Bool} {total start : ℕ}
    (hi : start < n) (h : before work below total start)
    (hbad : ¬ eligible below total (work ⟨start, hi⟩)) :
    before work below total (start + 1) := by
  intro i hb
  by_cases he : i.val = start
  · have heq : i = ⟨start, hi⟩ := Fin.ext he
    simpa only [heq] using hbad
  · exact h i (by omega)

private theorem index_bound (start remaining n : ℕ) (h : start + (remaining + 1) = n) :
    start < n := by omega

private theorem next_bound (start remaining n : ℕ) (h : start + (remaining + 1) = n) :
    (start + 1) + remaining = n := by omega

private theorem not_end {rT : Type} [BEq rT] (start remaining n : ℕ)
    (h : start + (remaining + 1) = n) :
    ((BaseLit.int (start : ℤ) : BaseLit rT) == .int (n : ℤ)) = false := by
  change ((start : ℤ) == n) = false
  exact beq_eq_false_iff_ne.mpr (by omega)

private theorem nat_lt_test (a b : ℕ) :
    decide ((a : ℤ) < (b : ℤ)) = decide (a < b) := by simp

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_find (E : CoPset) (l : Loc) {n : ℕ} (work : Fin n → ℕ)
    (total : ℕ) (below : Bool) (remaining start : ℕ) (h : start + remaining = n)
    (hbefore : before work below total start) :
    Array.owns l (List.ofFn ((fun value : ℕ => (Val.int value : Val rT)) ∘ work)) ⊢
      tglWp E pl(&(find (rT := rT) l n total) #int (start : ℤ) #bool below)
        (fun v => iprop(∃ r : ℤ, ⌜v = Val.int r ∧ result work below total r⌝ ∗
          Array.owns l (List.ofFn ((fun value : ℕ => (Val.int value : Val rT)) ∘ work)))) := by
  induction remaining generalizing start with
  | zero =>
    have he : start = n := h
    subst start
    iintro Harray
    twp_pures
    rw [beq_self_eq_true]
    twp_pures
    twp_value
    imodintro
    iexists (-1 : ℤ)
    isplit
    · ipureintro
      exact ⟨rfl, Or.inl ⟨rfl, before_end hbefore⟩⟩
    · iexact Harray
  | succ remaining IH =>
    let i : Fin n := ⟨start, index_bound start remaining n h⟩
    iintro Harray
    twp_pures
    rw [not_end start remaining n h]
    twp_pure
    twp_bind pl(!(#loc l +ₗ #int (start : ℤ)))
    iapply tglWp_wand
    isplitl [Harray]
    · iapply (Array.twp_load_ofFn E l
        ((fun value : ℕ => (Val.int value : Val rT)) ∘ work) i) $$ Harray
    iintro %v ⟨%hv, Harray⟩
    subst v
    by_cases hp : eligible below total (work i)
    · cases below <;> twp_pures
      all_goals
        simp [eligible] at hp
        rw [nat_lt_test]
        simp only [hp, _root_.decide_true]
        twp_pures
        twp_value
        imodintro
        iexists (start : ℤ)
        isplit
        · ipureintro
          exact ⟨rfl, Or.inr ⟨i, rfl, hp⟩⟩
        · iexact Harray
    · have hrec := IH (start + 1) (next_bound start remaining n h)
        (before_step (index_bound start remaining n h) hbefore hp)
      simp [-List.ofFn_succ, find, Exp.close, Exp.closeRec] at hrec
      cases below <;> twp_pures
      all_goals
        simp [eligible] at hp
        rw [nat_lt_test]
        simp only [Nat.not_lt.mpr hp, _root_.decide_false]
        iterate 2 twp_pure
        rw [← Nat.cast_add_one]
        simp only [Nat.cast_add_one, Exp.ofVal]
        iapply hrec $$ Harray

end specification

end SampLib.WalkerFind
