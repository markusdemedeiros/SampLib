module

public import SampLib.Combinatorial.Laws.ReservoirAdmissible

@[expose] public section

/-! # Predecessor weights of a reservoir state

The weight that one ticket step carries into a state, averaged over the `n + 1` tickets,
equals the closed-form weight of that state after one more stream position.
-/

open MeasureTheory Measure
open scoped ENNReal NNReal Classical

namespace SampLib.ReservoirLaw

noncomputable section

def weight (n k : ℕ) (s : Slots k) : ℝ≥0 :=
  if Admissible n k s then coefficient n k s else 0

theorem pmf_eq_coe_weight (n k : ℕ) (s : Slots k) : pmf n k s = weight n k s := by
  simp only [pmf, weight]
  split_ifs <;> simp

/-- Binomial counting supplies the common factor in both transition cases. -/
theorem coefficient_step {n k : ℕ} (hkn : k ≤ n) (t : Slots k) :
    ((n + 1 - k : ℕ) : ℝ≥0) * coefficient n k t / (n + 1 : ℕ) =
      coefficient (n + 1) k t := by
  have hc : (n.choose k : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hkn).ne'
  have hc' : ((n + 1).choose k : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (hkn.trans (Nat.le_succ n))).ne'
  have hf : ((lateCount t).factorial : ℝ≥0) ≠ 0 := by positivity
  have hn : (n + 1 : ℝ≥0) ≠ 0 := by positivity
  have hchoose : (n.choose k : ℝ≥0) * (n + 1) =
      ((n + 1).choose k : ℝ≥0) * (n + 1 - k : ℕ) := by
    exact_mod_cast Nat.choose_mul_succ_eq n k
  unfold coefficient
  field_simp
  simp only [Nat.cast_add, Nat.cast_one] at *
  simpa [mul_comm] using hchoose.symm

/-- The initial-coordinate predecessor carries m times the mass of a later predecessor. -/
theorem coefficient_restore_initial {n k : ℕ} {t : Slots k} (j : Fin k)
    (hj : k ≤ t j) :
    coefficient n k (Function.update t j j.val) =
      (lateCount t : ℝ≥0) * coefficient n k t := by
  have hm : 0 < lateCount t := Finset.card_pos.mpr ⟨j, by simp [hj]⟩
  have hfac : (lateCount t).factorial = lateCount t * (lateCount t - 1).factorial := by
    simpa [Nat.sub_add_cancel hm] using Nat.factorial_succ (lateCount t - 1)
  simp only [coefficient, lateCount_update_initial t j hj, hfac, Nat.cast_mul]
  by_cases hc : n.choose k = 0
  · simp [hc]
  · have hc' : (n.choose k : ℝ≥0) ≠ 0 := by exact_mod_cast hc
    have hm' : (lateCount t : ℝ≥0) ≠ 0 := by positivity
    have hf : ((lateCount t - 1).factorial : ℝ≥0) ≠ 0 := by positivity
    field_simp

/-- With m later items, the initial predecessor has mass m·b; the n+1−k−m missing later
predecessors each have mass b. The total incoming mass is therefore (n+1−k)·b. -/
theorem predecessor_weight_sum {n k : ℕ} (hkn : k ≤ n) {t : Slots k}
    (ht : Admissible (n + 1) k t) (j : Fin k) (hj : t j = n) :
    ∑ x ∈ Finset.range n, weight n k (Function.update t j x) =
      ((n + 1 - k : ℕ) : ℝ≥0) * coefficient n k t := by
  let a := coefficient n k (Function.update t j j.val)
  let b := coefficient n k t
  have hform (x : ℕ) (hx : x ∈ Finset.range n) :
      weight n k (Function.update t j x) =
        (if x = j.val then a else 0) + (if x ∈ available n k t then b else 0) := by
    have hx' := Finset.mem_range.mp hx
    rw [weight, admissible_predecessor ht j hj x hx']
    by_cases hxj : x = j.val
    · subst x
      have hnot : j.val ∉ available n k t := by
        intro h
        have := (Finset.mem_Ico.mp (Finset.mem_filter.mp h).1).1
        omega
      simp [hnot, a]
    · by_cases hxa : x ∈ available n k t
      · have hxk := (Finset.mem_Ico.mp (Finset.mem_filter.mp hxa).1).1
        simp [hxj, hxa, coefficient, lateCount_update_late t j x (by omega) hxk, b]
      · simp [hxj, hxa]
  rw [Finset.sum_congr rfl hform, Finset.sum_add_distrib]
  have hav : available n k t ⊆ Finset.range n := by
    intro x hx
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1).2
  have hfilter : (Finset.range n).filter (fun x => x ∈ available n k t) =
      available n k t := by
    ext x
    exact ⟨fun h => (Finset.mem_filter.mp h).2,
      fun h => Finset.mem_filter.mpr ⟨hav h, h⟩⟩
  have hfirst : (∑ x ∈ Finset.range n, if x = j.val then a else 0) = a := by
    simp [j.isLt.trans_le hkn]
  have hsecond : (∑ x ∈ Finset.range n, if x ∈ available n k t then b else 0) =
      (available n k t).card * b := by
    rw [← Finset.sum_filter, hfilter]
    simp
  rw [hfirst, hsecond]
  rw [show a = (lateCount t : ℝ≥0) * b from
    coefficient_restore_initial j (by omega), available_card hkn ht j hj]
  have hm : lateCount t ≤ n + 1 - k := lateCount_le ht
  rw [← add_mul]
  congr 1
  exact_mod_cast Nat.add_sub_of_le hm

theorem admissible_of_weight_ne_zero {n k : ℕ} {s : Slots k}
    (h : weight n k s ≠ 0) : Admissible n k s := by
  by_contra ha
  exact h (by simp [weight, ha])

/-- Every incoming tuple is admissible, including when the newest item replaces a slot. -/
theorem admissible_of_predecessor {n k : ℕ} (hkn : k ≤ n) {t : Slots k}
    (j : Fin k) (hj : t j = n) (x : ℕ) (h : Admissible n k (Function.update t j x)) :
    Admissible (n + 1) k t := by
  let ticket : Fin (n + 1) := ⟨j.val, j.isLt.trans_le (hkn.trans (Nat.le_succ n))⟩
  have he : advance n (Function.update t j x) ticket = t := by
    rw [advance_lt _ _ j.isLt]
    change Function.update (Function.update t j x) j n = t
    rw [Function.update_idem, ← hj, Function.update_eq_self]
  rw [← he]
  exact admissible_advance hkn h ticket

/-- The incoming mass is the same in both cases: reject the new item, or restore its slot. -/
theorem incoming_weight {n k : ℕ} (hkn : k ≤ n) (t : Slots k) :
    (((n + 1 - k : ℕ) : ℝ≥0) * weight n k t +
      ∑ j : Fin k, if t j = n then
        ∑ x ∈ Finset.range n, weight n k (Function.update t j x) else 0) / (n + 1 : ℕ) =
      weight (n + 1) k t := by
  by_cases ht : Admissible (n + 1) k t
  · by_cases hnew : ∃ j, t j = n
    · obtain ⟨j, hj⟩ := hnew
      have hold : ¬ Admissible n k t := fun h => Nat.lt_irrefl n (hj ▸ h.1 j)
      have he (i : Fin k) : t i = n ↔ i = j :=
        ⟨fun hi => ht.2.1 (hi.trans hj.symm), fun hi => hi ▸ hj⟩
      rw [show weight n k t = 0 by simp [weight, hold],
        show weight (n + 1) k t = coefficient (n + 1) k t by simp [weight, ht]]
      simp only [mul_zero, zero_add, he, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [predecessor_weight_sum hkn ht j hj]
      exact coefficient_step hkn t
    · have hold : Admissible n k t := by
        refine ⟨fun i => ?_, ht.2⟩
        have hi := ht.1 i
        have hn : t i ≠ n := fun h => hnew ⟨i, h⟩
        omega
      have hall (j : Fin k) : t j ≠ n := fun h => hnew ⟨j, h⟩
      simpa only [weight, hold, ht, hall, ite_true, ite_false, Finset.sum_const_zero,
        add_zero] using coefficient_step hkn t
  · have hold : ¬ Admissible n k t := fun h => ht (h.mono (Nat.le_succ n))
    have hzero (j : Fin k) : (if t j = n then
        ∑ x ∈ Finset.range n, weight n k (Function.update t j x) else 0) = 0 := by
      split_ifs with hj
      · apply Finset.sum_eq_zero
        intro x _
        by_contra hx
        exact ht (admissible_of_predecessor hkn j hj x (admissible_of_weight_ne_zero hx))
      · rfl
    rw [show weight n k t = 0 by simp [weight, hold],
      show weight (n + 1) k t = 0 by simp [weight, ht]]
    simp only [hzero, Finset.sum_const_zero, mul_zero, zero_add, zero_div]

end

end SampLib.ReservoirLaw
