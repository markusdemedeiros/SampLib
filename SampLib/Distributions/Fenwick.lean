module

public import SampLib.Distributions.FenwickLowBit
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! # Dyadic intervals underlying Fenwick trees

Node i stores the half-open interval ending at i whose length is its least set bit.
Binary lifting reads exactly one aligned dyadic block at each step.
-/

open scoped BigOperators

namespace FenwickMath

/-- Membership of a one-based weight position in a Fenwick node. -/
def contains (j i : ℕ) : Prop := i - lowBit i < j ∧ j ≤ i

instance (j i : ℕ) : Decidable (contains j i) :=
  inferInstanceAs (Decidable (i - lowBit i < j ∧ j ≤ i))

/-- A finite interval sum over zero-based weight positions. -/
def interval {n : ℕ} (w : Fin n → ℕ) (a b : ℕ) : ℕ :=
  ∑ j : Fin n with a ≤ j.val ∧ j.val < b, w j

def prefixSum {n : ℕ} (w : Fin n → ℕ) (i : ℕ) : ℕ :=
  ∑ j : Fin n with j.val < i, w j

def cell {n : ℕ} (w : Fin n → ℕ) (i : ℕ) : ℕ := interval w (i - lowBit i) i

@[simp] theorem prefixSum_zero {n : ℕ} (w : Fin n → ℕ) : prefixSum w 0 = 0 := by simp [prefixSum]

@[simp] theorem prefixSum_length {n : ℕ} (w : Fin n → ℕ) : prefixSum w n = ∑ j, w j := by
  simp [prefixSum]

@[simp] theorem cell_zero {n : ℕ} (w : Fin n → ℕ) : cell w 0 = 0 := by
  simp [cell, interval]

/-- Adjacent finite intervals partition a prefix, even when the upper endpoint exceeds n. -/
theorem prefixSum_add_interval {n : ℕ} (w : Fin n → ℕ) {i k : ℕ} (hik : i ≤ k) :
    prefixSum w i + interval w i k = prefixSum w k := by
  simp only [prefixSum, interval, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : j.val < i
  · simp [hi, hi.trans_le hik, Nat.not_le.mpr hi]
  · simp [hi, Nat.not_lt.mp hi]

theorem prefixSum_mono {n : ℕ} (w : Fin n → ℕ) {i k : ℕ} (hik : i ≤ k) :
    prefixSum w i ≤ prefixSum w k := by
  rw [← prefixSum_add_interval w hik]
  exact Nat.le_add_right _ _

/-- The node read by binary lifting stores precisely the next prefix block. -/
theorem prefixSum_add_cell {n : ℕ} (w : Fin n → ℕ) {i step : ℕ}
    (hbit : lowBit (i + step) = step) :
    prefixSum w i + cell w (i + step) = prefixSum w (i + step) := by
  rw [cell, hbit, Nat.add_sub_cancel]
  exact prefixSum_add_interval w (Nat.le_add_right _ _)

theorem prefixSum_add_aligned_cell {n : ℕ} (w : Fin n → ℕ) {i a : ℕ}
    (hi : 2 ^ (a + 1) ∣ i) :
    prefixSum w i + cell w (i + 2 ^ a) = prefixSum w (i + 2 ^ a) :=
  prefixSum_add_cell w (lowBit_aligned hi)

theorem lowBit_aligned_of_power {i step : ℕ} (hp : ∃ a, step = 2 ^ a)
    (hi : i % (2 * step) = 0) : lowBit (i + step) = step := by
  obtain ⟨a, rfl⟩ := hp
  apply lowBit_aligned
  simpa [pow_succ, mul_comm] using Nat.dvd_of_mod_eq_zero hi

theorem pow_le_lowBit {i a : ℕ} (hi : 0 < i) (hd : 2 ^ a ∣ i) : 2 ^ a ≤ lowBit i := by
  rw [lowBit, ite_eq_right hi.ne']
  exact pow_le_pow_right₀ (by decide) ((padicValNat_dvd_iff_le hi.ne').mp hd)

theorem two_lowBit_not_dvd {i : ℕ} (hi : 0 < i) : ¬ 2 * lowBit i ∣ i := by
  simpa [lowBit, hi.ne', pow_succ, mul_comm] using
    (pow_succ_padicValNat_not_dvd (p := 2) hi.ne')

/-- Advancing to the parent clears the current least set bit. -/
theorem two_lowBit_dvd_next {i : ℕ} (hi : 0 < i) : 2 * lowBit i ∣ i + lowBit i := by
  obtain ⟨m, hm⟩ := lowBit_dvd i
  have hodd : ¬ 2 ∣ m := by
    rintro ⟨t, ht⟩
    apply two_lowBit_not_dvd hi
    refine ⟨t, ?_⟩
    calc
      i = lowBit i * m := hm
      _ = lowBit i * (2 * t) := congrArg (fun x => lowBit i * x) ht
      _ = 2 * lowBit i * t := by ring
  have heven : 2 ∣ m + 1 := by omega
  obtain ⟨t, ht⟩ := heven
  refine ⟨t, ?_⟩
  calc
    i + lowBit i = lowBit i * m + lowBit i := congrArg (fun x => x + lowBit i) hm
    _ = lowBit i * (m + 1) := by ring
    _ = lowBit i * (2 * t) := congrArg (fun x => lowBit i * x) ht
    _ = 2 * lowBit i * t := by ring

theorem lowBit_next_ge {i : ℕ} (hi : 0 < i) :
    2 * lowBit i ≤ lowBit (i + lowBit i) := by
  have hd : 2 ^ (padicValNat 2 i + 1) ∣ i + lowBit i := by
    simpa [lowBit, hi.ne', pow_succ, mul_comm] using two_lowBit_dvd_next hi
  have h := pow_le_lowBit (by omega : 0 < i + lowBit i) hd
  simpa [lowBit, hi.ne', pow_succ, mul_comm] using h

theorem contains_self {i : ℕ} (hi : 0 < i) : contains i i := by
  have hp := lowBit_pos hi
  have hb := lowBit_le hi
  simp only [contains]
  omega

/-- Every node interval is contained in its parent's interval. -/
theorem contains_parent {j i : ℕ} (h : contains j i) : contains j (i + lowBit i) := by
  have hi : 0 < i := by have := h.1; have := h.2; omega
  have hp := lowBit_next_ge hi
  have hb := lowBit_le hi
  simp only [contains] at *
  omega

/-- Between two consecutive dyadic boundaries the least set bit fits inside the gap. -/
theorem lowBit_le_gap {i k a : ℕ} (hd : 2 ^ a ∣ i) (hik : i < k)
    (hki : k < i + 2 ^ a) : lowBit k ≤ k - i := by
  have hk : 0 < k := by omega
  by_cases ha : a ≤ padicValNat 2 k
  · have hdk : 2 ^ a ∣ k := (padicValNat_dvd_iff_le hk.ne').mpr ha
    have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hik) (Nat.dvd_sub hdk hd)
    omega
  · have hb : lowBit k ∣ 2 ^ a := by
      rw [lowBit, ite_eq_right hk.ne']
      exact pow_dvd_pow 2 (by omega)
    exact Nat.le_of_dvd (Nat.sub_pos_of_lt hik) (Nat.dvd_sub (lowBit_dvd k) (hb.trans hd))

/-- No node skipped on the way to the parent can contain an item of the current node. -/
theorem not_contains_between {j i k : ℕ} (h : contains j i) (hik : i < k)
    (hki : k < i + lowBit i) : ¬ contains j k := by
  have hi : 0 < i := by have := h.1; have := h.2; omega
  have hgap : lowBit k ≤ k - i := by
    apply lowBit_le_gap (show 2 ^ padicValNat 2 i ∣ i from pow_padicValNat_dvd) hik
    simpa only [lowBit, ite_eq_right hi.ne'] using hki
  simp only [contains] at *
  omega

theorem interval_singleton {n : ℕ} (w : Fin n → ℕ) (q : Fin n) :
    interval w q.val (q.val + 1) = w q := by
  have hs : (Finset.univ.filter (fun j : Fin n => q.val ≤ j.val ∧ j.val < q.val + 1)) =
      {q} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      apply Fin.ext
      omega
    · rintro rfl
      omega
  rw [interval, hs, Finset.sum_singleton]

theorem prefixSum_succ {n : ℕ} (w : Fin n → ℕ) (q : Fin n) :
    prefixSum w (q.val + 1) = prefixSum w q.val + w q := by
  rw [← prefixSum_add_interval w (Nat.le_succ q.val), interval_singleton]

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
