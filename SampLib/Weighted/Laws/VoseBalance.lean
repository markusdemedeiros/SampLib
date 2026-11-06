import SampLib.Weighted.Laws.VoseAdvance

/-! # The residual-mass invariant of Vose preprocessing

Finalized columns retain stale workspace entries. Their effective residual mass
is nevertheless `total`: the threshold and incoming alias deficits account for
all transfers into their categories.
-/

open Finset

namespace SampLib.VoseBalance

noncomputable section

variable {n total : ℕ} (weights : Fin n → ℕ)

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
