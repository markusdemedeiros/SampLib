module

public import SampLib.Distributions.SplittingPPS
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Ring.Nat

@[expose] public section

/-! # Interior boundaries for splitting PPS

The prescribed total rules out a saturated lower boundary and a zero upper
boundary. Their gap therefore supplies a strictly positive split amount.
-/

namespace SampLib.SplittingPPS

private theorem sum_parts (xs : List ℕ) (cut : ℕ) :
    (xs.take cut).sum + (xs.drop cut).sum = xs.sum := by
  rw [← List.sum_append, List.take_append_drop]

private theorem sum_upper (xs : List ℕ) (d : ℕ) (h : ∀ x ∈ xs, x ≤ d) :
    xs.sum ≤ xs.length * d := by
  simpa only [nsmul_eq_mul, Nat.cast_id] using List.sum_le_length_nsmul xs d h

private theorem sum_lower (xs : List ℕ) (d : ℕ) (h : ∀ x ∈ xs, d ≤ x) :
    xs.length * d ≤ xs.sum := by
  simpa only [nsmul_eq_mul, Nat.cast_id] using List.length_nsmul_le_sum xs d h

/-- A saturated lower boundary forces `count+1` full numerators; a zero upper
boundary leaves at most `count-1`. Both contradict the prescribed total. -/
theorem sorted_boundaries (xs : List ℕ) (cut count d : ℕ)
    (hcut : 0 < cut) (hcount : 0 < count) (hlen : xs.length = cut + count)
    (hd : 0 < d) (hs : xs.SortedLE) (hb : ∀ x ∈ xs, x ≤ d)
    (hmass : xs.sum = count * d) :
    xs[cut - 1]'(by omega) < d ∧ 0 < xs[cut]'(by omega) := by
  constructor
  · by_contra h
    have hlo : d ≤ xs[cut - 1]'(by omega) := Nat.le_of_not_gt h
    have htail : ∀ x ∈ xs.drop (cut - 1), d ≤ x := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.mp hx
      exact hlo.trans (hs.getElem_le_getElem_of_le (by omega))
    have hsum := sum_lower (xs.drop (cut - 1)) d htail
    have hlength : (xs.drop (cut - 1)).length = count + 1 := by
      simp only [List.length_drop]
      omega
    rw [hlength, Nat.add_mul, Nat.one_mul] at hsum
    have hparts := sum_parts xs (cut - 1)
    omega
  · by_contra h
    have hzero : xs[cut]'(by omega) = 0 := by omega
    have hhead : ∀ x ∈ xs.take (cut + 1), x ≤ 0 := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hx
      simpa only [hzero] using hs.getElem_le_getElem_of_le (i := j) (j := cut)
        (hi := by omega) (hj := by omega) (by omega)
    have hhead_sum := sum_upper (xs.take (cut + 1)) 0 hhead
    have htail_sum := sum_upper (xs.drop (cut + 1)) d
      (fun x hx => hb x (List.mem_of_mem_drop hx))
    have hlength : (xs.drop (cut + 1)).length = count - 1 := by
      simp only [List.length_drop]
      omega
    rw [hlength] at htail_sum
    have hparts := sum_parts xs (cut + 1)
    have hstrict : (count - 1) * d < count * d :=
      Nat.mul_lt_mul_of_pos_right (Nat.sub_lt hcount (by decide)) hd
    have htotal : xs.sum ≤ (count - 1) * d := by
      calc
        xs.sum = (xs.take (cut + 1)).sum + (xs.drop (cut + 1)).sum := hparts.symm
        _ ≤ 0 + (count - 1) * d :=
          Nat.add_le_add (by simpa only [Nat.mul_zero] using hhead_sum) htail_sum
        _ = _ := Nat.zero_add _
    rw [hmass] at htotal
    exact (Nat.not_le_of_gt hstrict) htotal

private theorem numerators_sorted (items : List Item) (ho : items.Pairwise ordered) :
    (items.map Prod.fst).SortedLE := by
  apply List.Pairwise.sortedLE
  have h : items.Pairwise (fun a b : Item => a.1 ≤ b.1) :=
    ho.imp (fun h => h)
  simpa only [List.pairwise_map] using h

/-- Labelled states inherit the same two strict boundary inequalities. -/
theorem interior_boundaries (items : List Item) (cut count d : ℕ)
    (hcut : 0 < cut) (hcount : 0 < count) (hlen : items.length = cut + count)
    (hd : 0 < d) (ho : items.Pairwise ordered) (hb : ∀ a ∈ items, a.1 ≤ d)
    (hmass : (items.map Prod.fst).sum = count * d) :
    (items[cut - 1]'(by omega)).1 < d ∧ 0 < (items[cut]'(by omega)).1 := by
  have h := sorted_boundaries (items.map Prod.fst) cut count d hcut hcount
    (by simpa only [List.length_map] using hlen) hd (numerators_sorted items ho)
    (by simpa only [List.forall_mem_map] using hb) hmass
  simpa only [List.getElem_map] using h


private theorem numerator_mono (items : List Item) (ho : items.Pairwise ordered)
    (i j : ℕ) (hi : i < items.length) (hj : j < items.length) (hij : i ≤ j) :
    (items[i]'hi).1 ≤ (items[j]'hj).1 := by
  rcases eq_or_lt_of_le hij with rfl | h
  · exact le_rfl
  · exact ho.rel_getElem_of_lt hi hj h

/-- Every bottom item lies below the lower split boundary. -/
theorem bottom_le_boundary (items : List Item) (cut : ℕ)
    (hcut : 0 < cut) (hlen : cut ≤ items.length) (ho : items.Pairwise ordered) :
    ∀ a ∈ items.take cut, a.1 ≤ (items[cut - 1]'(by omega)).1 := by
  intro a ha
  obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp ha
  exact numerator_mono items ho j (cut - 1) (by omega) (by omega) (by omega)

/-- Every top item lies above the upper split boundary. -/
theorem boundary_le_top (items : List Item) (cut : ℕ)
    (hlen : cut < items.length) (ho : items.Pairwise ordered) :
    ∀ a ∈ items.drop cut, (items[cut]'hlen).1 ≤ a.1 := by
  intro a ha
  obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.mp ha
  exact numerator_mono items ho cut (cut + j) hlen (by omega) (by omega)

/-- The source's minimum is positive, admissible, and decreases the denominator. -/
theorem split_amount_bounds (d low high : ℕ) (hlo : low < d) (hhi : 0 < high) :
    0 < min (d - low) high ∧ min (d - low) high ≤ d ∧ d - min (d - low) high < d := by
  have hpos : 0 < min (d - low) high := lt_min (Nat.sub_pos_of_lt hlo) hhi
  exact ⟨hpos, (min_le_left _ _).trans (Nat.sub_le _ _),
    Nat.sub_lt (lt_of_le_of_lt (Nat.zero_le low) hlo) hpos⟩

/-- The lower block fits the reduced denominator; subtraction handles the upper block. -/
theorem adjust_bounded (items : List Item) (cut d amount : ℕ)
    (hcut : 0 < cut) (hlen : cut ≤ items.length) (ho : items.Pairwise ordered)
    (hb : ∀ a ∈ items, a.1 ≤ d)
    (ha : amount ≤ d - (items[cut - 1]'(by omega)).1) :
    ∀ a ∈ adjust amount cut items, a.1 ≤ d - amount := by
  intro a hmem
  have ht : a ∈ trim amount cut items := (List.mem_insertionSort ordered).mp hmem
  rw [trim, List.mem_append] at ht
  rcases ht with hbottom | htop
  · have hl := bottom_le_boundary items cut hcut hlen ho a hbottom
    have hab := hb a (List.mem_of_mem_take hbottom)
    omega
  · obtain ⟨b, hbtop, rfl⟩ := List.mem_map.mp htop
    exact Nat.sub_le_sub_right (hb b (List.mem_of_mem_drop hbtop)) amount

/-- Reordering restores the source invariant after every rejected split. -/
theorem adjust_ordered (amount cut : ℕ) (items : List Item) :
    (adjust amount cut items).Pairwise ordered :=
  List.pairwise_insertionSort ordered _

/-- A rejected split changes probabilities, never the population of labels. -/
theorem adjust_labels (amount cut : ℕ) (items : List Item) :
    ((adjust amount cut items).map Prod.snd).Perm (items.map Prod.snd) := by
  have hlabels : (trim amount cut items).map Prod.snd = items.map Prod.snd := by
    simp only [trim, List.map_append, List.map_map, Function.comp_def]
    rw [← List.map_append, List.take_append_drop]
  simpa only [adjust, hlabels] using
    (List.perm_insertionSort ordered (trim amount cut items)).map Prod.snd

end SampLib.SplittingPPS
