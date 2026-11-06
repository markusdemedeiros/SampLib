import SampLib.Weighted.Laws.AliasMass

/-! # The Vose preprocessing state

The state holds the residual work, the small and large worklists, and the column
thresholds and aliases built so far. Its transitions are the initialization scan,
one pairing step, and the final flush.
-/

open Finset

namespace SampLib.VoseBalance

noncomputable section

structure State (n : ℕ) where
  work : Fin n → ℕ
  threshold : Fin n → ℕ
  target : Fin n → Fin n
  small : List (Fin n)
  large : List (Fin n)

namespace State

variable {n : ℕ}

def pending (s : State n) : Finset (Fin n) := (s.small ++ s.large).toFinset

def incoming (total : ℕ) (s : State n) (i : Fin n) : ℕ :=
  ∑ j, if s.target j = i then total - s.threshold j else 0

def effective (total : ℕ) (s : State n) (i : Fin n) : ℕ :=
  if i ∈ s.pending then s.work i else total

/-- Initialize one category and push its index onto the appropriate worklist. -/
def install (total : ℕ) (weights : Fin n → ℕ) (i : Fin n) (s : State n) : State n :=
  { s with
    work := Function.update s.work i (n * weights i)
    target := Function.update s.target i i
    small := if n * weights i < total then i :: s.small else s.small
    large := if n * weights i < total then s.large else i :: s.large }

/-- The initialization scan in its original index order. -/
def setup (total : ℕ) (weights : Fin n → ℕ) : List (Fin n) → State n → State n
  | [], s => s
  | i :: is, s => setup total weights is (install total weights i s)

theorem setup_work (total : ℕ) (weights : Fin n → ℕ) (is : List (Fin n))
    (s : State n) (i : Fin n) :
    (setup total weights is s).work i = if i ∈ is then n * weights i else s.work i := by
  induction is generalizing s with
  | nil => simp [setup]
  | cons j js ih =>
    simp only [setup, ih, install, List.mem_cons]
    by_cases hi : i ∈ js <;> by_cases hij : i = j <;> simp [hi, hij]

theorem setup_threshold (total : ℕ) (weights : Fin n → ℕ) (is : List (Fin n))
    (s : State n) : (setup total weights is s).threshold = s.threshold := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih => simpa only [setup, install] using ih (install total weights i s)

theorem setup_target (total : ℕ) (weights : Fin n → ℕ) (is : List (Fin n))
    (s : State n) (i : Fin n) :
    (setup total weights is s).target i = if i ∈ is then i else s.target i := by
  induction is generalizing s with
  | nil => simp [setup]
  | cons j js ih =>
    simp only [setup, ih, install, List.mem_cons]
    by_cases hi : i ∈ js <;> by_cases hij : i = j <;> simp [hi, hij]

theorem setup_small (total : ℕ) (weights : Fin n → ℕ) (is : List (Fin n))
    (s : State n) : (setup total weights is s).small =
      (is.filter (fun i => decide (n * weights i < total))).reverse ++ s.small := by
  induction is generalizing s with
  | nil => simp [setup]
  | cons i is ih =>
    by_cases hi : n * weights i < total <;>
      simp [setup, ih, install, hi, List.reverse_cons, List.append_assoc]

theorem setup_large (total : ℕ) (weights : Fin n → ℕ) (is : List (Fin n))
    (s : State n) : (setup total weights is s).large =
      (is.filter (fun i => decide (total ≤ n * weights i))).reverse ++ s.large := by
  induction is generalizing s with
  | nil => simp [setup]
  | cons i is ih =>
    by_cases hi : n * weights i < total
    · simp [setup, ih, install, hi, Nat.not_le.mpr hi]
    · simp [setup, ih, install, hi, Nat.le_of_not_gt hi, List.reverse_cons, List.append_assoc]

def blank (n total : ℕ) [NeZero n] : State n where
  work _ := 0
  threshold _ := total
  target _ := ⟨0, NeZero.pos n⟩
  small := []
  large := []

def initialized (total : ℕ) [NeZero n] (weights : Fin n → ℕ) : State n :=
  setup total weights (List.finRange n) (blank n total)

/-- Fill one small column and transfer its missing tickets from a large column. -/
def advance (total : ℕ) (s : State n) (lo hi : Fin n) : State n :=
  let remainder := s.work hi + s.work lo - total
  { work := Function.update s.work hi remainder
    threshold := Function.update s.threshold lo (s.work lo)
    target := Function.update s.target lo hi
    small := if remainder < total then hi :: s.small.tail else s.small.tail
    large := if remainder < total then s.large.tail else s.large }

/-- Every transfer removes one active column. -/
def finish (total : ℕ) (s : State n) : State n :=
  match _hs : s.small, _hg : s.large with
  | [], _ => s
  | _ :: _, [] => s
  | lo :: _, hi :: _ => finish total (s.advance total lo hi)
termination_by s.small.length + s.large.length
decreasing_by
  simp only [advance, _hs, _hg, List.tail_cons, List.length_cons]
  split <;> simp_all

end State

end

end SampLib.VoseBalance
