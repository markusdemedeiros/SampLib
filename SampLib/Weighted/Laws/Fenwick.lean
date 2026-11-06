module

public import SampLib.Weighted.Laws.FenwickIntervals

@[expose] public section

/-! # Fenwick selection and updates

Binary lifting reads exactly one aligned dyadic block at each step and stops at the
position whose cumulative-mass interval contains the target. Replacing one weight
changes exactly the nodes that contain it.
-/

open scoped BigOperators

namespace FenwickMath

/-- An inverse cumulative-mass interval; zero-weight positions have empty intervals. -/
def Selects {n : ℕ} (w : Fin n → ℕ) (target q : ℕ) : Prop :=
  q < n ∧ prefixSum w q ≤ target ∧ target < prefixSum w (q + 1)

theorem exists_selects {n : ℕ} (w : Fin n → ℕ) {target : ℕ}
    (ht : target < ∑ j, w j) : ∃ q, Selects w target q := by
  have hex : ∃ k, target < prefixSum w k := ⟨n, by simpa using ht⟩
  let k := Nat.find hex
  have hk : target < prefixSum w k := Nat.find_spec hex
  have hkn : k ≤ n := Nat.find_min' hex (by simpa using ht)
  have hkpos : 0 < k := by
    by_contra h
    have he : k = 0 := by omega
    simp [he] at hk
  have hprev : prefixSum w (k - 1) ≤ target := by
    exact Nat.le_of_not_gt (Nat.find_min hex (by omega : k - 1 < k))
  refine ⟨k - 1, ?_, hprev, ?_⟩
  · omega
  · simpa only [Nat.sub_add_cancel hkpos] using hk

theorem selects_unique {n : ℕ} {w : Fin n → ℕ} {target q r : ℕ}
    (hq : Selects w target q) (hr : Selects w target r) : q = r := by
  apply Nat.le_antisymm
  · by_contra h
    have hm := prefixSum_mono w (show r + 1 ≤ q by omega)
    have := hq.2.1
    have := hr.2.2
    omega
  · by_contra h
    have hm := prefixSum_mono w (show q + 1 ≤ r by omega)
    have := hr.2.1
    have := hq.2.2
    omega

theorem Selects.positive {n : ℕ} {w : Fin n → ℕ} {target q : ℕ}
    (h : Selects w target q) : 0 < w ⟨q, h.1⟩ := by
  have hs : prefixSum w (q + 1) = prefixSum w q + w ⟨q, h.1⟩ :=
    prefixSum_succ w ⟨q, h.1⟩
  have := h.2.1
  have := h.2.2
  omega

/-- If the candidate block fits in the remaining mass, the selected position is beyond it. -/
theorem next_le_selected {n : ℕ} (w : Fin n → ℕ) {target q i step remaining : ℕ}
    (hq : Selects w target q) (hr : prefixSum w i + remaining = target)
    (hbit : lowBit (i + step) = step) (hm : cell w (i + step) ≤ remaining) :
    i + step ≤ q := by
  have hc := prefixSum_add_cell w hbit
  by_contra h
  have hp := prefixSum_mono w (show q + 1 ≤ i + step by omega)
  have := hq.2.2
  omega

/-- If the candidate block exceeds the remaining mass, the selected position precedes it. -/
theorem selected_lt_next {n : ℕ} (w : Fin n → ℕ) {target q i step remaining : ℕ}
    (hq : Selects w target q) (hr : prefixSum w i + remaining = target)
    (hbit : lowBit (i + step) = step) (hm : remaining < cell w (i + step)) :
    q < i + step := by
  have hc := prefixSum_add_cell w hbit
  by_contra h
  have hp := prefixSum_mono w (show i + step ≤ q by omega)
  have := hq.2.1
  omega

/-- Finite-vector prefixes agree with the list representation used by categorical laws. -/
theorem prefixSum_eq_take_sum {n : ℕ} (w : Fin n → ℕ) (k : ℕ) :
    prefixSum w k = ((List.ofFn w).take k).sum := (List.sum_take_ofFn w k).symm

/-- Replacing one weight changes a finite sum by its signed difference exactly on its support. -/
theorem sum_update_int {n : ℕ} (w : Fin n → ℕ) (j : Fin n) (value : ℕ)
    (s : Finset (Fin n)) :
    ((∑ q ∈ s, Function.update w j value q : ℕ) : ℤ) =
      ((∑ q ∈ s, w q : ℕ) : ℤ) + (if j ∈ s then (value : ℤ) - w j else 0) := by
  by_cases hj : j ∈ s
  · rw [Finset.sum_update_of_mem hj,
      Finset.sum_eq_add_sum_sdiff_singleton_of_mem hj w, ite_eq_left hj]
    push_cast
    ring
  · rw [Finset.sum_update_of_notMem hj, ite_eq_right hj, add_zero]

theorem interval_update_int {n : ℕ} (w : Fin n → ℕ) (j : Fin n) (value a b : ℕ) :
    (interval (Function.update w j value) a b : ℤ) = (interval w a b : ℤ) +
      (if a ≤ j.val ∧ j.val < b then (value : ℤ) - w j else 0) := by
  simpa only [interval, Finset.mem_filter, Finset.mem_univ, true_and] using
    sum_update_int w j value (Finset.univ.filter (fun q => a ≤ q.val ∧ q.val < b))

theorem cell_mem_iff {n : ℕ} (j : Fin n) (i : ℕ) :
    i - lowBit i ≤ j.val ∧ j.val < i ↔ contains (j.val + 1) i := by
  simp only [contains]
  omega

/-- The signed replacement difference reaches precisely the ancestor nodes. -/
theorem cell_update_int {n : ℕ} (w : Fin n → ℕ) (j : Fin n) (value i : ℕ) :
    (cell (Function.update w j value) i : ℤ) = (cell w i : ℤ) +
      (if contains (j.val + 1) i then (value : ℤ) - w j else 0) := by
  simpa only [cell, cell_mem_iff] using interval_update_int w j value (i - lowBit i) i

theorem total_update_int {n : ℕ} (w : Fin n → ℕ) (j : Fin n) (value : ℕ) :
    ((∑ q, Function.update w j value q : ℕ) : ℤ) =
      ((∑ q, w q : ℕ) : ℤ) + (value : ℤ) - w j := by
  simpa only [Finset.mem_univ, ite_true, add_sub_assoc] using
    sum_update_int w j value Finset.univ

/-- Subtracting the accepted block preserves the original target mass. -/
theorem remaining_after_advance {n : ℕ} (w : Fin n → ℕ) {target i step remaining : ℕ}
    (hr : prefixSum w i + remaining = target) (hbit : lowBit (i + step) = step)
    (hm : cell w (i + step) ≤ remaining) :
    prefixSum w (i + step) + (remaining - cell w (i + step)) = target := by
  have hc := prefixSum_add_cell w hbit
  omega

/-- Halving a nonterminal dyadic search step gives the next dyadic step. -/
theorem power_half_cases {step : ℕ} (h : ∃ a, step = 2 ^ a) :
    step = 1 ∨ (∃ a, step / 2 = 2 ^ a) ∧ 2 * (step / 2) = step := by
  obtain ⟨a, rfl⟩ := h
  cases a with
  | zero => exact Or.inl rfl
  | succ a =>
    right
    exact ⟨⟨a, by simp [pow_succ]⟩, by simp [pow_succ, mul_comm]⟩

/-- Both possible next indices are aligned to the halved search step. -/
theorem aligned_half {i step : ℕ} (hi : i % (2 * step) = 0)
    (hstep : 2 * (step / 2) = step) :
    i % (2 * (step / 2)) = 0 ∧ (i + step) % (2 * (step / 2)) = 0 := by
  have hd : step ∣ i := (show step ∣ 2 * step from ⟨2, by ring⟩).trans
    (Nat.dvd_of_mod_eq_zero hi)
  have hz := Nat.mod_eq_zero_of_dvd hd
  rw [hstep]
  exact ⟨hz, by simp [hz]⟩

end FenwickMath
