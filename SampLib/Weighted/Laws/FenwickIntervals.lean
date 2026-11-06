module

public import SampLib.Weighted.Laws.FenwickLowBit
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! # Dyadic intervals underlying Fenwick trees

Node i stores the half-open interval ending at i whose length is its least set bit.
A position that a node contains also lies in that node's parent.
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

end FenwickMath
