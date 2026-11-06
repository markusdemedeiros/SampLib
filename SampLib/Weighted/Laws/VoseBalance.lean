import SampLib.Weighted.Laws.AliasMass

/-! # The residual-mass invariant of Vose preprocessing

Finalized columns retain stale workspace entries. Their effective residual mass
is nevertheless `total`: the threshold and incoming alias deficits account for
all transfers into their categories.
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

variable {n total : ℕ} (weights : Fin n → ℕ)

/-- Residual work and assigned incoming tickets jointly conserve each category's mass. -/
structure Invariant (total : ℕ) (s : State n) : Prop where
  nodup : (s.small ++ s.large).Nodup
  small_lt : ∀ i ∈ s.small, s.work i < total
  large_le : ∀ i ∈ s.large, total ≤ s.work i
  threshold_le : ∀ i, s.threshold i ≤ total
  pending_default : ∀ i ∈ s.pending, s.threshold i = total ∧ s.target i = i
  conservation : ∀ i, n * weights i + (total - s.threshold i) =
    s.effective total i + s.incoming total i

/-- The initialization scan gives every category its scaled mass and one worklist entry. -/
theorem initialized_invariant [NeZero n] :
    Invariant weights total (State.initialized total weights) := by
  let s := State.initialized total weights
  have hw (i : Fin n) : s.work i = n * weights i := by
    simp [s, State.initialized, State.setup_work]
  have ht (i : Fin n) : s.threshold i = total := by
    simp [s, State.initialized, State.setup_threshold, State.blank]
  have ha (i : Fin n) : s.target i = i := by
    simp [s, State.initialized, State.setup_target]
  have hs : s.small = ((List.finRange n).filter
      (fun i => decide (n * weights i < total))).reverse := by
    simp [s, State.initialized, State.setup_small, State.blank]
  have hl : s.large = ((List.finRange n).filter
      (fun i => decide (total ≤ n * weights i))).reverse := by
    simp [s, State.initialized, State.setup_large, State.blank]
  have hsmall (i : Fin n) : i ∈ s.small ↔ n * weights i < total := by simp [hs]
  have hlarge (i : Fin n) : i ∈ s.large ↔ total ≤ n * weights i := by simp [hl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs, hl]
    apply List.Nodup.append
    · exact List.nodup_reverse.mpr ((List.nodup_finRange n).filter _)
    · exact List.nodup_reverse.mpr ((List.nodup_finRange n).filter _)
    · apply List.disjoint_left.mpr
      intro i hi hj
      have hilt : n * weights i < total := by simpa using hi
      have hjge : total ≤ n * weights i := by simpa using hj
      omega
  · intro i hi
    rw [hw]
    exact (hsmall i).mp hi
  · intro i hi
    rw [hw]
    exact (hlarge i).mp hi
  · intro i
    exact (ht i).le
  · intro i _
    exact ⟨ht i, ha i⟩
  · intro i
    have hp : i ∈ s.pending := by
      simp only [State.pending, List.mem_toFinset, List.mem_append, hsmall, hlarge]
      exact lt_or_ge _ _
    change n * weights i + (total - s.threshold i) =
      s.effective total i + s.incoming total i
    simp [State.effective, State.incoming, hp, ht, hw]

/-- Each alias edge contributes its deficit to exactly one category. -/
theorem sum_incoming (s : State n) :
    ∑ i, s.incoming total i = ∑ j, (total - s.threshold j) := by
  simp only [State.incoming]
  rw [Finset.sum_comm]
  simp

/-- The total effective residual mass stays equal to the total column capacity. -/
theorem sum_effective (s : State n) (h : Invariant weights total s)
    (htotal : ∑ i, weights i = total) :
    ∑ i, s.effective total i = n * total := by
  have hm : (∑ i : Fin n, (n * weights i + (total - s.threshold i))) =
      ∑ i : Fin n, (s.effective total i + s.incoming total i) :=
    Finset.sum_congr rfl (fun i _ => h.conservation i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, htotal, sum_incoming] at hm
  omega

/-- Filling a small column adds exactly its missing mass to the chosen alias. -/
theorem incoming_advance (s : State n) (lo hi i : Fin n)
    (hlo : s.threshold lo = total) :
    (s.advance total lo hi).incoming total i = s.incoming total i +
      if hi = i then total - s.work lo else 0 := by
  unfold State.incoming
  calc
    _ = ∑ j, ((if s.target j = i then total - s.threshold j else 0) +
        if j = lo then (if hi = i then total - s.work lo else 0) else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = lo
      · subst j
        simp [State.advance, hlo]
      · simp [State.advance, hj]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

/-- Both worklist branches remove precisely the completed small column. -/
theorem advance_pending (s : State n) (lo hi : Fin n) (small large : List (Fin n))
    (hs : s.small = lo :: small) (hl : s.large = hi :: large)
    (hd : (s.small ++ s.large).Nodup) :
    (s.advance total lo hi).pending = s.pending.erase lo := by
  have hnot : lo ∉ small ++ hi :: large :=
    (List.nodup_cons.mp (by simpa only [hs, hl, List.cons_append] using hd)).1
  have hnot' : lo ∉ small ∧ lo ≠ hi ∧ lo ∉ large := by
    simpa only [List.mem_append, List.mem_cons, not_or] using hnot
  ext i
  by_cases hr : s.work hi + s.work lo - total < total <;>
    simp only [State.pending, State.advance, hs, hl, List.tail_cons, hr,
      ite_true, ite_false, List.mem_toFinset, List.mem_append, List.mem_cons,
      Finset.mem_erase] <;> aesop

/-- The workspace entry of a completed column becomes logically full, without a heap write. -/
theorem advance_effective (s : State n) (lo hi : Fin n) (small large : List (Fin n))
    (hs : s.small = lo :: small) (hl : s.large = hi :: large)
    (hd : (s.small ++ s.large).Nodup) (i : Fin n) :
    (s.advance total lo hi).effective total i =
      if i = lo then total else if i = hi then s.work hi + s.work lo - total
      else s.effective total i := by
  have hp := advance_pending s lo hi small large hs hl hd (total := total)
  have hhi : hi ∈ s.pending := by simp [State.pending, hl]
  have hne : hi ≠ lo := by
    have hnot := (List.nodup_cons.mp
      (by simpa only [hs, hl, List.cons_append] using hd)).1
    intro heq
    exact hnot (by simp [heq])
  simp only [State.effective, hp, Finset.mem_erase]
  by_cases hlo : i = lo <;> by_cases hih : i = hi <;> simp_all [State.advance]

/-- Moving the surviving donor between stacks preserves uniqueness of active indices. -/
theorem advance_nodup (s : State n) (lo hi : Fin n) (small large : List (Fin n))
    (hs : s.small = lo :: small) (hl : s.large = hi :: large)
    (hd : (s.small ++ s.large).Nodup) :
    ((s.advance total lo hi).small ++ (s.advance total lo hi).large).Nodup := by
  have hrest : (small ++ hi :: large).Nodup :=
    (List.nodup_cons.mp (by simpa only [hs, hl, List.cons_append] using hd)).2
  by_cases hr : s.work hi + s.work lo - total < total
  · have hp : (small ++ hi :: large).Perm (hi :: (small ++ large)) := List.perm_middle
    simpa only [State.advance, hs, hl, List.tail_cons, hr, ite_true, List.cons_append] using
      hp.nodup_iff.mp hrest
  · simpa only [State.advance, hs, hl, List.tail_cons, hr, ite_false] using hrest

/-- Filling one column and debiting its donor preserve every category's total mass. -/
theorem advance_conservation (s : State n) (h : Invariant weights total s)
    (lo hi : Fin n) (small large : List (Fin n))
    (hs : s.small = lo :: small) (hl : s.large = hi :: large) (i : Fin n) :
    n * weights i + (total - (s.advance total lo hi).threshold i) =
      (s.advance total lo hi).effective total i + (s.advance total lo hi).incoming total i := by
  have hlo : lo ∈ s.pending := by simp [State.pending, hs]
  have hhi : hi ∈ s.pending := by simp [State.pending, hl]
  have hloCut := (h.pending_default lo hlo).1
  have hhiCut := (h.pending_default hi hhi).1
  have hloSmall := h.small_lt lo (by simp [hs])
  have hhiLarge := h.large_le hi (by simp [hl])
  have hne : lo ≠ hi := by intro he; rw [he] at hloSmall; omega
  have hmlo : n * weights lo = s.work lo + s.incoming total lo := by
    simpa only [hloCut, Nat.sub_self, Nat.add_zero, State.effective, ite_eq_left hlo] using
      h.conservation lo
  have hmhi : n * weights hi = s.work hi + s.incoming total hi := by
    simpa only [hhiCut, Nat.sub_self, Nat.add_zero, State.effective, ite_eq_left hhi] using
      h.conservation hi
  rw [advance_effective s lo hi small large hs hl h.nodup i,
    incoming_advance s lo hi i hloCut]
  simp only [State.advance]
  by_cases hio : i = lo
  · subst i
    simp only [Function.update_self, ite_true, hne, Ne.symm hne, ite_false, Nat.add_zero]
    omega
  · by_cases hih : i = hi
    · subst i
      simp only [Function.update_of_ne (Ne.symm hne), Ne.symm hne,
        ite_true, ite_false, hhiCut, Nat.sub_self, Nat.add_zero]
      omega
    · simpa only [Function.update_of_ne hio, hio, hih, Ne.symm hih,
        ite_false, Nat.add_zero] using h.conservation i

/-- A transfer finalizes one small column and reclassifies its remaining donor. -/
theorem advance_invariant (s : State n) (h : Invariant weights total s)
    (lo hi : Fin n) (small large : List (Fin n))
    (hs : s.small = lo :: small) (hl : s.large = hi :: large) :
    Invariant weights total (s.advance total lo hi) := by
  have hloSmall := h.small_lt lo (by simp [hs])
  have hhiLarge := h.large_le hi (by simp [hl])
  have hhiNot : hi ∉ large := (List.nodup_cons.mp
    (by simpa only [hl] using h.nodup.of_append_right)).1
  refine ⟨advance_nodup s lo hi small large hs hl h.nodup, ?_, ?_, ?_, ?_,
    advance_conservation weights s h lo hi small large hs hl⟩
  · intro i hm
    by_cases hr : s.work hi + s.work lo - total < total
    · have hm' : i = hi ∨ i ∈ small := by simpa [State.advance, hs, hr] using hm
      rcases hm' with rfl | hm'
      · simpa [State.advance] using hr
      · have hold := h.small_lt i (by simp [hs, hm'])
        have hne : i ≠ hi := by intro he; rw [he] at hold; omega
        simpa [State.advance, hne] using hold
    · have hm' : i ∈ small := by simpa [State.advance, hs, hr] using hm
      have hold := h.small_lt i (by simp [hs, hm'])
      have hne : i ≠ hi := by intro he; rw [he] at hold; omega
      simpa [State.advance, hne] using hold
  · intro i hm
    by_cases hr : s.work hi + s.work lo - total < total
    · have hm' : i ∈ large := by simpa [State.advance, hl, hr] using hm
      have hne : i ≠ hi := by intro he; subst i; exact hhiNot hm'
      simpa [State.advance, hne] using h.large_le i (by simp [hl, hm'])
    · have hm' : i = hi ∨ i ∈ large := by simpa [State.advance, hl, hr] using hm
      rcases hm' with rfl | hm'
      · simpa [State.advance] using Nat.le_of_not_gt hr
      · by_cases he : i = hi
        · subst i
          simpa [State.advance] using Nat.le_of_not_gt hr
        · simpa [State.advance, he] using h.large_le i (by simp [hl, hm'])
  · intro i
    by_cases he : i = lo
    · subst i
      simpa [State.advance] using hloSmall.le
    · simpa [State.advance, he] using h.threshold_le i
  · intro i hm
    rw [advance_pending s lo hi small large hs hl h.nodup] at hm
    obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hm
    simpa [State.advance, hne] using h.pending_default i hm

private theorem equal_of_total (f : Fin n → ℕ) (hsum : ∑ i, f i = n * total)
    (hside : (∀ i, f i ≤ total) ∨ (∀ i, total ≤ f i)) : ∀ i, f i = total := by
  rcases hside with hle | hge
  · have hz : (∑ i, (total - f i)) = 0 := by
      rw [Finset.sum_tsub_distrib _ (fun i _ => hle i)]
      simp [hsum]
    intro i
    have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (total - f j))
      (Finset.mem_univ i)
    rw [hz] at hi
    have := hle i
    omega
  · have hz : (∑ i, (f i - total)) = 0 := by
      rw [Finset.sum_tsub_distrib _ (fun i _ => hge i), hsum]
      simp
    intro i
    have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (f j - total))
      (Finset.mem_univ i)
    rw [hz] at hi
    have := hge i
    omega

/-- When either worklist is empty, every effective residual equals one full column. -/
theorem terminal_mass (s : State n) (h : Invariant weights total s)
    (htotal : ∑ i, weights i = total) (hstop : s.small = [] ∨ s.large = []) (i : Fin n) :
    s.threshold i + s.incoming total i = n * weights i := by
  have heff : ∀ j, s.effective total j = total := by
    apply equal_of_total _ (sum_effective weights s h htotal)
    rcases hstop with hs | hl
    · right
      intro j
      by_cases hj : j ∈ s.pending
      · simpa only [State.effective, ite_eq_left hj] using
          h.large_le j (by simpa [State.pending, hs] using hj)
      · simp [State.effective, hj]
    · left
      intro j
      by_cases hj : j ∈ s.pending
      · simpa only [State.effective, ite_eq_left hj] using
          (h.small_lt j (by simpa [State.pending, hl] using hj)).le
      · simp [State.effective, hj]
  have hc := h.conservation i
  rw [heff] at hc
  have := h.threshold_le i
  omega

/-- Every recursive transfer preserves the residual-mass invariant. -/
theorem finish_invariant (s : State n) (h : Invariant weights total s) :
    Invariant weights total (s.finish total) := by
  revert h
  induction s using State.finish.induct total with
  | case1 s hs =>
    intro h
    have heq : s.finish total = s := by rw [State.finish, hs]
    simpa only [heq] using h
  | case2 s lo small hs hl =>
    intro h
    have heq : s.finish total = s := by rw [State.finish, hs, hl]
    simpa only [heq] using h
  | case3 s lo small hi large hs hl ih =>
    intro h
    have heq : s.finish total = (s.advance total lo hi).finish total := by
      rw [State.finish, hs, hl]
    rw [heq]
    exact ih (advance_invariant weights s h lo hi small large hs hl)

/-- Preprocessing stops only when one of the two worklists has emptied. -/
theorem finish_stops (s : State n) :
    (s.finish total).small = [] ∨ (s.finish total).large = [] := by
  induction s using State.finish.induct total with
  | case1 s hs =>
    have heq : s.finish total = s := by rw [State.finish, hs]
    exact Or.inl (by simpa only [heq] using hs)
  | case2 s lo small hs hl =>
    have heq : s.finish total = s := by rw [State.finish, hs, hl]
    exact Or.inr (by simpa only [heq] using hl)
  | case3 s lo small hi large hs hl ih =>
    have heq : s.finish total = (s.advance total lo hi).finish total := by
      rw [State.finish, hs, hl]
    simpa only [heq] using ih

/-- The final thresholds and aliases account for exactly the original category masses. -/
theorem finish_mass (s : State n) (h : Invariant weights total s)
    (htotal : ∑ i, weights i = total) (i : Fin n) :
    (s.finish total).threshold i + (s.finish total).incoming total i = n * weights i :=
  terminal_mass weights (s.finish total) (finish_invariant weights s h) htotal (finish_stops s) i

/-- The finalized arrays form a valid alias table. -/
def finishedTable (s : State n) (h : Invariant weights total s) : AliasMass.Table n total :=
  ⟨(s.finish total).threshold, (s.finish total).target, (finish_invariant weights s h).threshold_le⟩

theorem finishedTable_mass (s : State n) (h : Invariant weights total s)
    (htotal : ∑ i, weights i = total) (i : Fin n) :
    (finishedTable weights s h).mass i = n * weights i := by
  change (s.finish total).threshold i + (s.finish total).incoming total i = n * weights i
  exact finish_mass weights s h htotal i

end

end SampLib.VoseBalance
