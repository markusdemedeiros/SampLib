import SampLib.Distributions.DyadicGroups
import SampLib.Distributions.AliasMass

/-! # Monotone weights and their dyadic envelopes

The source visits the heavier end of either sorted orientation first. The
first weight in each dyadic block therefore bounds every proposal in that block.
-/

open Finset
open scoped ENNReal

namespace SampLib.SortedWeights

/-- The source accepts either monotone orientation, including equal neighbours. -/
def Sorted (ws : List ℕ) : Prop := ws.Pairwise (· ≤ ·) ∨ ws.Pairwise (· ≥ ·)

def ascending (ws : List ℕ) : Bool := decide (ws[0]?.getD 0 ≤ ws[ws.length - 1]?.getD 0)

def Ordered (asc : Bool) (a b : ℕ) : Prop := if asc then a ≤ b else b ≤ a

def index (n : ℕ) (asc : Bool) (offset : ℕ) : ℕ := if asc then n - 1 - offset else offset

def value (ws : List ℕ) (asc : Bool) (offset : ℕ) : ℕ := ws[index ws.length asc offset]?.getD 0

def pivot (n : ℕ) (asc : Bool) (k : ℕ) : ℕ :=
  if asc then n - DyadicGroups.lower k else DyadicGroups.lower k - 1

def envelope (ws : List ℕ) (asc : Bool) (k : ℕ) : ℕ := ws[pivot ws.length asc k]?.getD 0

/-- Pairwise order also compares equal positions. -/
theorem ordered_at (ws : List ℕ) (asc : Bool) (h : ws.Pairwise (Ordered asc))
    (i j : ℕ) (hi : i < ws.length) (hj : j < ws.length) (hij : i ≤ j) :
    Ordered asc ws[i] ws[j] := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · cases asc <;> simp [Ordered]
  · exact h.rel_getElem_of_lt hi hj hlt

/-- Endpoint comparison selects a valid orientation even when descending endpoints tie. -/
theorem chosen_order (ws : List ℕ) (h : Sorted ws) : ws.Pairwise (Ordered (ascending ws)) := by
  by_cases hn : ws = []
  · subst ws
    simp
  · have hn' : 0 < ws.length := List.length_pos_iff.mpr hn
    have hlast : ws.length - 1 < ws.length := by omega
    have hchoice : ascending ws = decide (ws[0] ≤ ws[ws.length - 1]) := by
      simp only [ascending, List.getElem?_eq_getElem hn', List.getElem?_eq_getElem hlast,
        Option.getD_some]
    rcases h with hup | hdown
    · have ho : ws.Pairwise (Ordered true) := by exact hup
      have he := ordered_at ws true ho 0 (ws.length - 1) hn' hlast (by omega)
      change ws[0] ≤ ws[ws.length - 1] at he
      rw [hchoice, decide_eq_true he]
      exact ho
    · by_cases he : ws[0] ≤ ws[ws.length - 1]
      · rw [hchoice, decide_eq_true he]
        apply List.pairwise_iff_getElem.mpr
        intro i j hi hj hij
        have ho : ws.Pairwise (Ordered false) := by
          exact hdown
        have hfirst := ordered_at ws false ho 0 i hn' hi (by omega)
        have hlast' := ordered_at ws false ho j (ws.length - 1) hj hlast (by omega)
        change ws[i] ≤ ws[0] at hfirst
        change ws[ws.length - 1] ≤ ws[j] at hlast'
        change ws[i] ≤ ws[j]
        omega
      · rw [hchoice, decide_eq_false he]
        exact hdown

theorem index_lt (n offset : ℕ) (asc : Bool) (ho : offset < n) : index n asc offset < n := by
  cases asc <;> simp only [index, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem pivot_lt (n k : ℕ) (asc : Bool) (hk : k < n.size) : pivot n asc k < n := by
  have hl := DyadicGroups.lower_pos k
  have hn : DyadicGroups.lower k ≤ n := Nat.lt_size.mp hk
  cases asc <;> simp only [pivot, Bool.false_eq_true, ite_false, ite_true] <;> omega

/-- The pivot is the heaviest weight throughout the selected group. -/
theorem envelope_bound (ws : List ℕ) (asc : Bool) (hs : ws.Pairwise (Ordered asc))
    (k r : ℕ) (hk : k < ws.length.size) (hr : r < DyadicGroups.width ws.length k) :
    value ws asc (DyadicGroups.lower k - 1 + r) ≤ envelope ws asc k := by
  have ho := DyadicGroups.offset_lt ws.length k r hk hr
  have hi := index_lt ws.length (DyadicGroups.lower k - 1 + r) asc ho
  have hp := pivot_lt ws.length k asc hk
  have hl := DyadicGroups.lower_pos k
  have hn := Nat.lt_size.mp hk
  simp only [value, envelope, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hp,
    Option.getD_some]
  cases asc with
  | false =>
    have h := ordered_at ws false hs (pivot ws.length false k)
      (index ws.length false (DyadicGroups.lower k - 1 + r)) hp hi (by
        simp only [pivot, index, Bool.false_eq_true, ite_false]
        omega)
    exact h
  | true =>
    have h := ordered_at ws true hs (index ws.length true (DyadicGroups.lower k - 1 + r))
      (pivot ws.length true k) hi hp (by
        simp only [pivot, index, ite_true]
        omega)
    exact h

/-- The optional indexing convention gives precisely the original finite weight sum. -/
theorem sum_weights (ws : List ℕ) : (∑ i ∈ range ws.length, ws[i]?.getD 0) = ws.sum := by
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ i : Fin ws.length, ws[i.val] := by
      apply sum_congr rfl
      intro i _
      rw [List.getElem?_eq_getElem i.isLt, Option.getD_some]
    _ = _ := Fin.sum_univ_getElem ws

/-- The categorical continuation sum in finite-range form. -/
theorem weightedSum_range (ws : List ℕ) (F : ℕ → ℝ≥0∞) :
    WeightedChoice.weightedSum ws F = ∑ i ∈ range ws.length, (ws[i]?.getD 0 : ℝ≥0∞) * F i := by
  rw [AliasMass.weightedSum_fin]
  calc
    _ = ∑ i : Fin ws.length, (ws[i.val]?.getD 0 : ℝ≥0∞) * F i := by
      apply sum_congr rfl
      intro i _
      rw [List.get_eq_getElem, List.getElem?_eq_getElem i.isLt, Option.getD_some]
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun i => (ws[i]?.getD 0 : ℝ≥0∞) * F i) ws.length

/-- Reversal changes only traversal order, leaving total mass unchanged. -/
theorem value_sum (ws : List ℕ) (asc : Bool) :
    (∑ i ∈ range ws.length, value ws asc i) = ws.sum := by
  cases asc
  · simpa only [value, index, Bool.false_eq_true, ite_false] using sum_weights ws
  · simpa only [value, index, ite_true] using
      (Finset.sum_range_reflect (fun i => ws[i]?.getD 0) ws.length).trans (sum_weights ws)

/-- Both orientations preserve all labelled output credits, including infinity. -/
theorem value_credit (ws : List ℕ) (asc : Bool) (F : ℕ → ℝ≥0∞) :
    (∑ i ∈ range ws.length, (value ws asc i : ℝ≥0∞) * F (index ws.length asc i)) =
      WeightedChoice.weightedSum ws F := by
  rw [weightedSum_range]
  cases asc
  · simp only [value, index, Bool.false_eq_true, ite_false]
  · simpa only [value, index, ite_true] using
      Finset.sum_range_reflect (fun i => (ws[i]?.getD 0 : ℝ≥0∞) * F i) ws.length

end SampLib.SortedWeights
