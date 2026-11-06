module

public import SampLib.Common.Laws.PoissonStopping

@[expose] public section

/-! # Live paths of the Duchon–Duvignau tree

`liveCount a m b` counts the parity-constrained subsets with `m` omitted labels and
largest omitted label `b`. Its up and down recurrences match the tree's two moves.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.PoissonTree

noncomputable section

open Finset

/-- Live paths indexed by the number of omitted labels and their largest label. -/
def liveCount (a m b : ℕ) : ℕ :=
  if m = 0 then if b = 0 then 1 else 0
  else if Even m ∧ m ≤ a ∧ b ≠ 0 ∧ b ≤ a then (b - 1).choose (m - 1) else 0

@[simp] theorem liveCount_zero_omitted (a b : ℕ) :
    liveCount a 0 b = if b = 0 then 1 else 0 := by simp [liveCount]

@[simp] theorem liveCount_zero_boundary (a m : ℕ) :
    liveCount a m 0 = if m = 0 then 1 else 0 := by simp [liveCount]

theorem liveCount_up (a m b : ℕ) (hb : b ≤ a) :
    liveCount (a + 1) m b = liveCount a m b := by
  by_cases hm : m = 0
  · simp [liveCount, hm]
  by_cases hb0 : b = 0
  · simp [liveCount, hm, hb0]
  by_cases he : Even m
  · by_cases hma : m ≤ a
    · simp [liveCount, hm, hb0, he, hma, hb, show m ≤ a + 1 by omega,
        show b ≤ a + 1 by omega]
    · have hz : (b - 1).choose (m - 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [liveCount, hm, hb0, he, hma, hz]
  · simp [liveCount, hm, he]

theorem liveCount_down (a m : ℕ) :
    liveCount (a + 1) (m + 2) (a + 1) =
      ∑ b ∈ range (a + 1), (a - b) * liveCount a m b := by
  have heq : Even (m + 2) ↔ Even m := by simp [Nat.even_add]
  by_cases he : Even m
  · have hleft : liveCount (a + 1) (m + 2) (a + 1) = a.choose (m + 1) := by
      have he' := heq.mpr he
      by_cases hma : m + 2 ≤ a + 1
      · simp [liveCount, he', hma]
      · have hz : a.choose (m + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        simp [liveCount, he', hma, hz]
    rw [hleft]
    by_cases hm : m = 0
    · subst m
      rw [sum_range_succ']
      simp
    by_cases hma : m ≤ a
    · rw [sum_range_succ']
      simp only [liveCount_zero_boundary, hm, ite_false, mul_zero, add_zero]
      rw [show (∑ i ∈ range a, (a - (i + 1)) * liveCount a m (i + 1)) =
          ∑ i ∈ range a, (a - (i + 1)) * i.choose (m - 1) by
        apply sum_congr rfl
        intro i hi
        simp [liveCount, hm, he, hma, show i + 1 ≤ a by have := mem_range.mp hi; omega]]
      exact (sum_live_predecessors a m (by omega)).symm
    · have hz : a.choose (m + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [liveCount, hm, he, hma, hz]
  · have he' : ¬Even (m + 2) := fun h => he (heq.mp h)
    have hm : m ≠ 0 := by intro h; subst m; simp at he
    simp [liveCount, he, he', hm]

theorem liveCount_support {a m b : ℕ} (h : liveCount a m b ≠ 0) :
    m ≤ a ∧ m ≤ b ∧ b ≤ a := by
  by_cases hm : m = 0
  · subst m
    have hb : b = 0 := by
      by_contra hb
      simp [liveCount, hb] at h
    subst b
    omega
  · by_cases hvalid : Even m ∧ m ≤ a ∧ b ≠ 0 ∧ b ≤ a
    · have hc : (b - 1).choose (m - 1) ≠ 0 := by simpa [liveCount, hm, hvalid] using h
      have hmb := Nat.choose_ne_zero_iff.mp hc
      exact ⟨hvalid.2.1, by omega, hvalid.2.2.2⟩
    · simp [liveCount, hm, hvalid] at h

theorem liveCount_above_size (a m b : ℕ) (h : a < m) : liveCount a m b = 0 := by
  by_contra hc
  have := (liveCount_support hc).1
  omega

theorem liveCount_diagonal (a b : ℕ) : (a - b) * liveCount a a b = 0 := by
  by_cases h : liveCount a a b = 0
  · rw [h, mul_zero]
  · have hb := (liveCount_support h).2.1
    simp [Nat.sub_eq_zero_of_le hb]

/-- Splitting a live layer into its fixed-point and deletion children. -/
theorem live_sum_succ (a : ℕ) (G : ℕ → ℕ → ℝ≥0∞) :
    (∑ m ∈ range (a + 2), ∑ b ∈ range (a + 2),
      (liveCount (a + 1) m b : ℝ≥0∞) * G m b) =
      ∑ m ∈ range (a + 1), ∑ b ∈ range (a + 1),
        (liveCount a m b : ℝ≥0∞) * (G m b + (a - b : ℕ) * G (m + 2) (a + 1)) := by
  have hup : (∑ m ∈ range (a + 2), ∑ b ∈ range (a + 1),
      (liveCount (a + 1) m b : ℝ≥0∞) * G m b) =
      ∑ m ∈ range (a + 1), ∑ b ∈ range (a + 1),
        (liveCount a m b : ℝ≥0∞) * G m b := by
    rw [show a + 2 = (a + 1) + 1 by omega, sum_range_succ]
    have hlast : (∑ b ∈ range (a + 1),
        (liveCount (a + 1) (a + 1) b : ℝ≥0∞) * G (a + 1) b) = 0 := by
      apply sum_eq_zero
      intro b hb
      rw [liveCount_up a (a + 1) b (by have := mem_range.mp hb; omega),
        liveCount_above_size a (a + 1) b (by omega)]
      simp
    rw [hlast, add_zero]
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro b hb
    rw [liveCount_up a m b (by have := mem_range.mp hb; omega)]
  have hdown : (∑ m ∈ range (a + 2),
      (liveCount (a + 1) m (a + 1) : ℝ≥0∞) * G m (a + 1)) =
      ∑ m ∈ range (a + 1), ∑ b ∈ range (a + 1),
        (liveCount a m b : ℝ≥0∞) * (a - b : ℕ) * G (m + 2) (a + 1) := by
    have hzero : liveCount (a + 1) 0 (a + 1) = 0 := by simp
    have hone : liveCount (a + 1) 1 (a + 1) = 0 := by simp [liveCount]
    have hfirst : (∑ m ∈ range 2,
        (liveCount (a + 1) m (a + 1) : ℝ≥0∞) * G m (a + 1)) = 0 := by
      simp [sum_range_succ, hzero, hone]
    conv_lhs => rw [show a + 2 = 2 + a by omega, sum_range_add, hfirst, zero_add]
    rw [sum_range_succ]
    have hlast : (∑ b ∈ range (a + 1),
        (liveCount a a b : ℝ≥0∞) * (a - b : ℕ) * G (a + 2) (a + 1)) = 0 := by
      apply sum_eq_zero
      intro b hb
      have h := liveCount_diagonal a b
      have hc : (liveCount a a b : ℝ≥0∞) * (a - b : ℕ) = 0 := by
        exact_mod_cast (by simpa [Nat.mul_comm] using h)
      rw [hc, zero_mul]
    rw [hlast, add_zero]
    apply sum_congr rfl
    intro m hm
    rw [show 2 + m = m + 2 by omega, liveCount_down, Nat.cast_sum, sum_mul]
    apply sum_congr rfl
    intro b hb
    simp only [Nat.cast_mul]
    ring
  calc
    _ = (∑ m ∈ range (a + 2), ∑ b ∈ range (a + 1),
        (liveCount (a + 1) m b : ℝ≥0∞) * G m b) +
        ∑ m ∈ range (a + 2),
          (liveCount (a + 1) m (a + 1) : ℝ≥0∞) * G m (a + 1) := by
      conv_lhs => arg 2; ext m; rw [sum_range_succ]
      rw [sum_add_distrib]
    _ = _ := by
      rw [hup, hdown]
      simp only [mul_add, sum_add_distrib, mul_assoc]

/-- Count the stopping edges of a fixed-cardinality parity layer. -/
theorem sum_stopping_edges (a m : ℕ) :
    ∑ b ∈ range (a + 1), b * liveCount a m b =
      if Even m ∧ m ≤ a then m * (a + 1).choose (m + 1) else 0 := by
  by_cases hm : m = 0
  · subst m
    rw [sum_range_succ']
    simp
  by_cases he : Even m
  · by_cases hma : m ≤ a
    · rw [ite_eq_left ⟨he, hma⟩, sum_range_succ']
      simp only [zero_mul, add_zero]
      rw [show (∑ i ∈ range a, (i + 1) * liveCount a m (i + 1)) =
          ∑ i ∈ range a, (i + 1) * i.choose (m - 1) by
        apply sum_congr rfl
        intro i hi
        simp [liveCount, hm, he, hma, show i + 1 ≤ a by have := mem_range.mp hi; omega]]
      exact sum_largest_label a m (by omega)
    · simp [liveCount, hm, he, hma]
  · simp [liveCount, hm, he]

/-- Factorial normalization leaves the Poisson coefficient at each stopping layer. -/
theorem normalized_stopping_edges (a m : ℕ) (hm : m ≤ a) :
    ((m * (a + 1).choose (m + 1) : ℕ) : ℝ≥0∞) / (a + 1).factorial =
      (m : ℝ≥0∞) / (((a - m).factorial * (m + 1).factorial : ℕ) : ℝ≥0∞) := by
  have hf : (a + 1).factorial =
      (a + 1).choose (m + 1) * (m + 1).factorial * (a - m).factorial := by
    simpa only [Nat.add_sub_add_right] using
      (Nat.choose_mul_factorial_mul_factorial (show m + 1 ≤ a + 1 by omega)).symm
  have hc : ((a + 1).choose (m + 1) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show m + 1 ≤ a + 1 by omega)).ne'
  rw [hf]
  simp only [Nat.cast_mul]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    ENNReal.mul_div_mul_left (m : ℝ≥0∞)
      (((m + 1).factorial : ℝ≥0∞) * (a - m).factorial) hc (by simp)

end

end SampLib.PoissonTree
