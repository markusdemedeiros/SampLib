import SampLib.Distributions.AliasMass

/-! # Walker alias preprocessing

Deficits in completed columns are charged to their alias targets. The remaining
work has constant total; each transfer completes at least one unfinished column.
-/

open Finset
open scoped Classical

namespace SampLib.WalkerAlias

noncomputable section

structure State (n total : ℕ) where
  work : Fin n → ℕ
  table : AliasMass.Table n total

namespace State

variable {n total : ℕ}

structure Valid (weight : Fin n → ℕ) (s : State n total) : Prop where
  conservation : ∀ i, n * weight i + (total - s.table.threshold i) =
    s.work i + s.table.incoming i
  untouched : ∀ i, s.work i ≠ total → s.table.threshold i = total ∧ s.table.target i = i

def initial (weight : Fin n → ℕ) (total : ℕ) : State n total where
  work i := n * weight i
  table := ⟨fun _ => total, id, fun _ => le_rfl⟩

theorem valid_initial (weight : Fin n → ℕ) (total : ℕ) : Valid weight (initial weight total) where
  conservation i := by simp [initial, AliasMass.Table.incoming]
  untouched i _ := ⟨rfl, rfl⟩

theorem sum_incoming (t : AliasMass.Table n total) :
    (∑ i : Fin n, t.incoming i) = ∑ i : Fin n, (total - t.threshold i) := by
  simp only [AliasMass.Table.incoming]
  rw [Finset.sum_comm]
  simp

/-- Sending a deficit to its alias preserves the total remaining work. -/
theorem total_work {weight : Fin n → ℕ} {s : State n total}
    (hw : ∑ i, weight i = total) (hv : Valid weight s) :
    ∑ i, s.work i = n * total := by
  have h := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    hv.conservation i)
  simp only [Finset.sum_add_distrib] at h
  rw [← Finset.mul_sum, hw, sum_incoming] at h
  omega

/-- A column below the common total forces another column above it. -/
theorem exists_large {weight : Fin n → ℕ} {s : State n total}
    (hw : ∑ i, weight i = total) (hv : Valid weight s) (i : Fin n)
    (hi : s.work i < total) : ∃ j, total < s.work j := by
  by_contra h
  have hle (j : Fin n) : s.work j ≤ total :=
    Nat.le_of_not_gt (fun hj => h ⟨j, hj⟩)
  have hlt := Finset.sum_lt_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hle j)
    ⟨i, Finset.mem_univ i, hi⟩
  simp only [total_work hw hv, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id, lt_self_iff_false] at hlt

/-- With no small columns left, every remaining column has exactly the common total. -/
theorem terminal_mass {weight : Fin n → ℕ} {s : State n total}
    (hw : ∑ i, weight i = total) (hv : Valid weight s) (hlarge : ∀ i, total ≤ s.work i) :
    ∀ i, s.table.mass i = n * weight i := by
  have hsum : (∑ _ : Fin n, total) = ∑ i, s.work i := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_id] using
      (total_work hw hv).symm
  have heq := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    hlarge i)).mp hsum
  intro i
  have hwork := heq i (Finset.mem_univ i)
  have hmass := hv.conservation i
  have hcut := s.table.threshold_le i
  unfold AliasMass.Table.mass
  omega

/-- Complete a small column and charge its missing tickets to the donor column. -/
def transfer (s : State n total) (i j : Fin n) (hi : s.work i < total) : State n total where
  work := Function.update (Function.update s.work j (s.work j + s.work i - total)) i total
  table :=
    { threshold := Function.update s.table.threshold i (s.work i)
      target := Function.update s.table.target i j
      threshold_le x := by
        by_cases hx : x = i
        · subst x
          simpa only [Function.update_self] using hi.le
        · simpa only [Function.update_of_ne hx] using s.table.threshold_le x }

theorem incoming_transfer (s : State n total) (i j : Fin n) (hi : s.work i < total)
    (hcut : s.table.threshold i = total) (x : Fin n) :
    (transfer s i j hi).table.incoming x =
      s.table.incoming x + if j = x then total - s.work i else 0 := by
  let f : Fin n → ℕ := fun c => if s.table.target c = x then total - s.table.threshold c else 0
  let v := if j = x then total - s.work i else 0
  have hz : f i = 0 := by simp [f, hcut]
  have hs : (∑ c, f c) = ∑ c ∈ Finset.univ \ {i}, f c := by
    simpa only [hz, zero_add] using
      Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) f
  have hf : (fun c : Fin n =>
      if Function.update s.table.target i j c = x then
        total - Function.update s.table.threshold i (s.work i) c else 0) =
      Function.update f i v := by
    funext c
    by_cases hc : c = i <;> simp [f, v, hc]
  change (∑ c : Fin n, if Function.update s.table.target i j c = x then
    total - Function.update s.table.threshold i (s.work i) c else 0) = (∑ c, f c) + v
  rw [hf, Finset.sum_update_of_mem (Finset.mem_univ i), ← hs, add_comm]

/-- The same conservation argument permits a donor exactly at the common total. -/
theorem valid_transfer {weight : Fin n → ℕ} {s : State n total} (hv : Valid weight s)
    (i j : Fin n) (hi : s.work i < total) (hj : total ≤ s.work j)
    (hdefault : s.table.threshold j = total ∧ s.table.target j = j) :
    Valid weight (transfer s i j hi) := by
  have hne : i ≠ j := by intro h; subst j; omega
  have hcut := (hv.untouched i hi.ne).1
  constructor
  · intro x
    have hold := hv.conservation x
    rw [incoming_transfer s i j hi hcut]
    by_cases hxi : x = i
    · subst x
      simp only [transfer, Function.update_self, ite_eq_right (Ne.symm hne), add_zero]
      omega
    · by_cases hxj : x = j
      · subst x
        simp only [transfer, Function.update_of_ne hxi, Function.update_self,
          ite_true]
        omega
      · simpa only [transfer, Function.update_of_ne hxi, Function.update_of_ne hxj,
          ite_eq_right (Ne.symm hxj), add_zero] using hold
  · intro x hx
    by_cases hxi : x = i
    · subst x
      simp [transfer] at hx
    · by_cases hxj : x = j
      · subst x
        simpa only [transfer, Function.update_of_ne hxi] using hdefault
      · have hxold : s.work x ≠ total := by simpa [transfer, hxi, hxj] using hx
        simpa only [transfer, Function.update_of_ne hxi] using hv.untouched x hxold

def pending (s : State n total) : Finset (Fin n) :=
  Finset.univ.filter (fun i => s.work i ≠ total)

/-- Walker's strict donor removes a pending column and creates no new one. -/
theorem pending_transfer_lt (s : State n total) (i j : Fin n)
    (hi : s.work i < total) (hj : total < s.work j) :
    (pending (transfer s i j hi)).card < (pending s).card := by
  have hsub : pending (transfer s i j hi) ⊆ pending s := by
    intro x hx
    simp only [pending, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    by_cases hxi : x = i
    · subst x
      simp [transfer] at hx
    · by_cases hxj : x = j
      · subst x
        exact hj.ne'
      · simpa [transfer, hxi, hxj] using hx
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
  intro heq
  have hold : i ∈ pending s := by simp [pending, hi.ne]
  have hnew : i ∉ pending (transfer s i j hi) := by
    intro hh
    apply (Finset.mem_filter.mp hh).2
    simp only [transfer, Function.update_self]
  exact hnew (heq.symm ▸ hold)

end State

end

end SampLib.WalkerAlias
