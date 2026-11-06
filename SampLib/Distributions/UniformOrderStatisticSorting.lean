module

public import SampLib.Distributions.UniformOrderStatistic
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.FinRange

@[expose] public section

/-! # Tagged sorting identifies the continuous rank

The tags retain their physical handles; only their order changes. Sortedness and
a permutation of all tags suffice to identify the selected latent coordinate.
-/

namespace SampLib.UniformOrderStatistic

noncomputable section

/-- In a sorted list the j-th entry is below a threshold iff at least j+1 entries are. -/
theorem sorted_get_le_iff {α : Type} (f : α → ℝ) (l : List α)
    (hs : l.Pairwise (fun i j => f i ≤ f j)) (j : Fin l.length) (t : ℝ) :
    f (l.get j) ≤ t ↔ j.val + 1 ≤ (l.filter (fun i => decide (f i ≤ t))).length := by
  induction l with
  | nil => exact j.elim0
  | cons a l ih =>
    rcases List.pairwise_cons.mp hs with ⟨ha, hl⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · change f a ≤ t ↔ 1 ≤ ((a :: l).filter (fun i => decide (f i ≤ t))).length
      by_cases ht : f a ≤ t
      · simp [ht]
      · have hnone : l.filter (fun i => decide (f i ≤ t)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro b hb
          simpa only [decide_eq_true_eq] using not_le.mpr (lt_of_lt_of_le (lt_of_not_ge ht) (ha b hb))
        simp [ht, hnone]
    · change f (l.get j) ≤ t ↔ j.val + 1 + 1 ≤
        ((a :: l).filter (fun i => decide (f i ≤ t))).length
      have hhead : f a ≤ f (l.get j) := ha _ (List.get_mem _ _)
      by_cases ht : f a ≤ t
      · simpa [ht] using ih hl j
      · have hnone : l.filter (fun i => decide (f i ≤ t)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro b hb
          simpa only [decide_eq_true_eq] using not_le.mpr (lt_of_lt_of_le (lt_of_not_ge ht) (ha b hb))
        have hlast : ¬f (l.get j) ≤ t := not_le.mpr
          (lt_of_lt_of_le (lt_of_not_ge ht) hhead)
        simpa [ht, hnone] using hlast

/-- A sorted permutation of all tags selects the canonical rank, including at ties. -/
theorem rank_eq_sorted_get (n k : ℕ) (hk : 0 < k ∧ k ≤ n) (x : Fin n → ℝ)
    (tags : List (Fin n)) (hp : tags.Perm (List.finRange n))
    (hs : tags.Pairwise (fun i j => x i ≤ x j)) :
    rank n k hk x = x (tags.get ⟨k - 1, by simpa [hp.length_eq] using
      (show k - 1 < n by omega)⟩) := by
  classical
  have hnodup : tags.Nodup := hp.nodup_iff.mpr (List.nodup_finRange n)
  have hall : tags.toFinset = Finset.univ := by
    ext i
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact hp.mem_iff.mpr (List.mem_finRange i)
  have hcount (t : ℝ) :
      (tags.filter (fun i => decide (x i ≤ t))).length =
        (Finset.univ.filter (fun i => x i ≤ t)).card := by
    rw [← List.toFinset_card_of_nodup (hnodup.filter _), List.toFinset_filter, hall]
    rfl
  apply le_antisymm
  · rw [rank_le_iff]
    have h := (sorted_get_le_iff x tags hs ⟨k - 1, by
      simpa [hp.length_eq] using (show k - 1 < n by omega)⟩
      (x (tags.get ⟨k - 1, by simpa [hp.length_eq] using
        (show k - 1 < n by omega)⟩))).mp le_rfl
    rw [hcount] at h
    simpa [Nat.sub_add_cancel hk.1] using h
  · have h := (rank_le_iff n k hk x (rank n k hk x)).mp le_rfl
    rw [← hcount] at h
    apply (sorted_get_le_iff x tags hs _ _).mpr
    simpa [Nat.sub_add_cancel hk.1] using h

end

end SampLib.UniformOrderStatistic
