module

public import SampLib.Combinatorial.Laws.ReservoirTarget

@[expose] public section

/-! # Admissible reservoir states

A fresh stream position preserves admissibility. If the newest position sits in slot `j`,
the admissible predecessors put back either the initial item `j` or an `available`
position, and `available_card` counts the latter.
-/

open MeasureTheory Measure
open scoped ENNReal NNReal Classical

namespace SampLib.ReservoirLaw

noncomputable section

theorem Admissible.mono {n m k : ℕ} {s : Slots k} (h : Admissible n k s)
    (hnm : n ≤ m) : Admissible m k s :=
  ⟨fun i => (h.1 i).trans_le hnm, h.2⟩

/-- Fresh stream positions preserve distinctness and the fixed initial slots. -/
theorem admissible_advance {n k : ℕ} (hkn : k ≤ n) {s : Slots k}
    (h : Admissible n k s) (j : Fin (n + 1)) : Admissible (n + 1) k (advance n s j) := by
  by_cases hj : j.val < k
  · rw [advance_lt s j hj]
    let a : Fin k := ⟨j.val, hj⟩
    change Admissible (n + 1) k (Function.update s a n)
    refine ⟨?_, ?_, ?_⟩
    · intro i
      by_cases hi : i = a
      · subst i; simp
      · simp only [Function.update_of_ne hi]
        exact (h.1 i).trans_le (Nat.le_succ _)
    · intro i l hil
      by_cases hi : i = a <;> by_cases hl : l = a
      · exact hi.trans hl.symm
      · subst i
        simp only [Function.update_self, Function.update_of_ne hl] at hil
        have := h.1 l
        omega
      · subst l
        simp only [Function.update_self, Function.update_of_ne hi] at hil
        have := h.1 i
        omega
      · apply h.2.1
        simpa only [Function.update_of_ne hi, Function.update_of_ne hl] using hil
    · intro i hi
      by_cases hai : i = a
      · subst i; simp only [Function.update_self] at hi; omega
      · rw [Function.update_of_ne hai] at hi ⊢
        exact h.2.2 i hi
  · rw [advance_ge s j (by omega)]
    exact h.mono (Nat.le_succ _)

/-- Replacing one coordinate preserves injectivity exactly when its new value is fresh. -/
theorem injective_update_iff {k : ℕ} {s : Slots k} (hs : Function.Injective s)
    (j : Fin k) (x : ℕ) :
    Function.Injective (Function.update s j x) ↔ ∀ i, i ≠ j → s i ≠ x := by
  constructor
  · intro h i hi hx
    apply hi
    apply h
    simp [Function.update_of_ne hi, hx]
  · intro h i l hil
    by_cases hi : i = j <;> by_cases hl : l = j
    · exact hi.trans hl.symm
    · subst i
      simp only [Function.update_self, Function.update_of_ne hl] at hil
      exact (h l hl hil.symm).elim
    · subst l
      simp only [Function.update_self, Function.update_of_ne hi] at hil
      exact (h i hi hil).elim
    · apply hs
      simpa only [Function.update_of_ne hi, Function.update_of_ne hl] using hil

/-- Later positions available to restore the coordinate occupied by the newest item. -/
def available (n k : ℕ) (t : Slots k) : Finset ℕ :=
  (Finset.Ico k n).filter (fun x => ∀ i, t i ≠ x)

theorem admissible_predecessor {n k : ℕ} {t : Slots k}
    (ht : Admissible (n + 1) k t) (j : Fin k) (hj : t j = n) (x : ℕ) (hx : x < n) :
    Admissible n k (Function.update t j x) ↔ x = j.val ∨ x ∈ available n k t := by
  have hother (i : Fin k) (hi : i ≠ j) : t i < n := by
    have hne : t i ≠ n := fun h => hi (ht.2.1 (h.trans hj.symm))
    have := ht.1 i
    omega
  constructor
  · intro h
    by_cases hxk : x < k
    · left
      simpa using h.2.2 j (by simpa using hxk)
    · right
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hx⟩, ?_⟩
      intro i hi
      by_cases hij : i = j
      · subst i; omega
      · have hneq := (injective_update_iff ht.2.1 j x).mp h.2.1 i hij
        exact hneq hi
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i
      by_cases hi : i = j
      · subst i; simpa using hx
      · simpa only [Function.update_of_ne hi] using hother i hi
    · apply (injective_update_iff ht.2.1 j x).mpr
      intro i hi hix
      rcases h with rfl | h
      · have hti : t i < k := by omega
        have hpin := ht.2.2 i hti
        exact hi (Fin.ext (hpin.symm.trans hix))
      · exact (Finset.mem_filter.mp h).2 i hix
    · intro i hi
      by_cases hij : i = j
      · subst i
        simp only [Function.update_self] at hi ⊢
        rcases h with h | h
        · exact h
        · have := (Finset.mem_Ico.mp (Finset.mem_filter.mp h).1).1
          omega
      · rw [Function.update_of_ne hij] at hi ⊢
        exact ht.2.2 i hi

theorem lateCount_update_late {k : ℕ} (t : Slots k) (j : Fin k) (x : ℕ)
    (hj : k ≤ t j) (hx : k ≤ x) :
    lateCount (Function.update t j x) = lateCount t := by
  unfold lateCount
  congr 1
  ext i
  by_cases hi : i = j <;> simp [hi, hj, hx]

theorem lateCount_update_initial {k : ℕ} (t : Slots k) (j : Fin k) (hj : k ≤ t j) :
    lateCount (Function.update t j j.val) = lateCount t - 1 := by
  have he : Finset.univ.filter (fun i => k ≤ Function.update t j j.val i) =
      (Finset.univ.filter (fun i => k ≤ t i)).erase j := by
    ext i
    by_cases hi : i = j <;> simp [hi, j.isLt]
  unfold lateCount
  rw [he, Finset.card_erase_of_mem (by simp [hj])]

theorem lateCount_le {n k : ℕ} {t : Slots k} (ht : Admissible n k t) :
    lateCount t ≤ n - k := by
  let late := Finset.univ.filter (fun i => k ≤ t i)
  have hsub : late.image t ⊆ Finset.Ico k n := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp hi).2, ht.1 i⟩
  simpa [late, lateCount, Nat.card_Ico, Finset.card_image_of_injective _ ht.2.1] using
    Finset.card_le_card hsub

/-- All previous later items except the newest occupy distinct forbidden values. -/
theorem available_card {n k : ℕ} (hkn : k ≤ n) {t : Slots k}
    (ht : Admissible (n + 1) k t) (j : Fin k) (hj : t j = n) :
    (available n k t).card = n + 1 - k - lateCount t := by
  let old := (Finset.univ.filter (fun i => k ≤ t i)).erase j
  have hjmem : j ∈ Finset.univ.filter (fun i => k ≤ t i) := by simp [hj, hkn]
  have hold : old.card = lateCount t - 1 := Finset.card_erase_of_mem hjmem
  have hsub : old.image t ⊆ Finset.Ico k n := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hij, hi⟩ := Finset.mem_erase.mp hi
    have hlt := ht.1 i
    have hne : t i ≠ n := fun h => hij (ht.2.1 (h.trans hj.symm))
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp hi).2, by omega⟩
  have he : available n k t = Finset.Ico k n \ old.image t := by
    ext x
    simp only [available, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_image]
    constructor
    · rintro ⟨hx, hall⟩
      exact ⟨hx, fun ⟨i, _, hi⟩ => hall i hi⟩
    · rintro ⟨hx, hnone⟩
      refine ⟨hx, fun i hi => ?_⟩
      by_cases hij : i = j
      · subst i
        have := (Finset.mem_Ico.mp hx).2
        omega
      · apply hnone
        refine ⟨i, Finset.mem_erase.mpr ⟨hij, ?_⟩, hi⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          have := (Finset.mem_Ico.mp hx).1
          omega⟩
  have himage : (old.image t).card = lateCount t - 1 := by
    rw [Finset.card_image_of_injective _ ht.2.1, hold]
  have hbound := Finset.card_le_card hsub
  have hm : 0 < lateCount t := by
    exact Finset.card_pos.mpr ⟨j, hjmem⟩
  rw [he, Finset.card_sdiff_of_subset hsub, himage, Nat.card_Ico]
  rw [Nat.card_Ico, himage] at hbound
  omega

end

end SampLib.ReservoirLaw
