module

public import SampLib.Weighted.Laws.OptimalEncoding
public import Mathlib.Data.Nat.Size

@[expose] public section

/-! # The source's finite search for a cyclic denominator

After its first candidate, the search retains a genuine cyclic denominator at
least the requested total. Each later candidate either improves that witness or
ends the search. Zeros in the weight vector do not enter this argument.
-/

namespace SampLib.OptimalParameters

open OptimalEncoding

/-- Exact arithmetic counterpart of the source's `parameters` loop. -/
def select (k total l bestL bestTotal : ℕ) : ℕ × ℕ :=
  if _h : k ≤ l then (bestL, bestTotal) else
    let d := denominator k l
    if d = total then (l, d) else
      if d < total then (bestL, bestTotal) else select k total (l + 1) l d
termination_by k - l

/-- A selected prefix lies inside the scanned width and dominates the target total. -/
def Valid (k total : ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 < k ∧ p.2 = denominator k p.1 ∧ total ≤ p.2

theorem select_valid (k total l bestL bestTotal : ℕ)
    (hbest : Valid k total (bestL, bestTotal)) :
    Valid k total (select k total l bestL bestTotal) := by
  rw [select]
  dsimp only
  split_ifs with hkl heq hlt
  · exact hbest
  · exact ⟨by omega, rfl, heq.ge⟩
  · exact hbest
  · exact select_valid k total (l + 1) l (denominator k l) ⟨by omega, rfl, by omega⟩
termination_by k - l

theorem initial_valid (k total : ℕ) (hk : 0 < k) (hceil : total < 2 ^ k) :
    Valid k total (select k total 0 k (2 ^ k)) := by
  rw [select]
  dsimp only
  simp only [Nat.not_le.mpr hk]
  by_cases heq : denominator k 0 = total
  · simp only [heq, ite_true]
    exact ⟨hk, by simp [heq], le_rfl⟩
  · have hle : total ≤ denominator k 0 := by simp [denominator]; omega
    simp only [heq, ite_false, Nat.not_lt.mpr hle]
    exact select_valid k total 1 0 (denominator k 0) ⟨hk, rfl, hle⟩

/-- The actual preprocessing chooses its bit width from the strictly positive total. -/
def selected (total : ℕ) : ℕ × ℕ := select total.size total 0 total.size (2 ^ total.size)

theorem selected_valid {total : ℕ} (htotal : 0 < total) :
    Valid total.size total (selected total) :=
  initial_valid total.size total (Nat.size_pos.mpr htotal) (Nat.lt_size_self total)

theorem selected_positive {total : ℕ} (htotal : 0 < total) :
    0 < (selected total).2 := lt_of_lt_of_le htotal (selected_valid htotal).2.2

theorem selected_lt_ceiling {total : ℕ} (htotal : 0 < total) :
    (selected total).2 < 2 ^ total.size := by
  rw [(selected_valid htotal).2.1]
  exact Nat.sub_lt (by positivity) (by positivity)

end SampLib.OptimalParameters
