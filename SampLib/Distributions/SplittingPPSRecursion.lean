module

public import SampLib.Distributions.SplittingPPS

@[expose] public section

/-! # Structural equations for the splitting update -/

namespace SampLib.SplittingPPS

@[simp] theorem trim_nil (amount cut : ℕ) : trim amount cut [] = [] := by simp [trim]

@[simp] theorem trim_zero (amount : ℕ) (items : List Item) :
    trim amount 0 items = items.map (fun a => (a.1 - amount, a.2)) := by simp [trim]

@[simp] theorem trim_cons_succ (amount cut : ℕ) (item : Item) (items : List Item) :
    trim amount (cut + 1) (item :: items) = item :: trim amount cut items := by
  simp only [trim, List.take_succ_cons, List.drop_succ_cons, List.cons_append]

@[simp] theorem adjust_nil (amount cut : ℕ) : adjust amount cut [] = [] := by
  simp only [adjust, trim_nil, List.insertionSort_nil]

@[simp] theorem adjust_cons_succ (amount cut : ℕ) (item : Item) (items : List Item) :
    adjust amount (cut + 1) (item :: items) =
      (adjust amount cut items).orderedInsert ordered item := by
  simp only [adjust, trim_cons_succ, List.insertionSort_cons]

@[simp] theorem adjust_cons_zero (amount : ℕ) (item : Item) (items : List Item) :
    adjust amount 0 (item :: items) =
      (adjust amount 0 items).orderedInsert ordered (item.1 - amount, item.2) := by
  simp only [adjust, trim_zero, List.map_cons, List.insertionSort_cons]

/-- Negative remaining counts all describe the same upper block. -/
theorem adjust_cons_int (amount : ℕ) (remaining : ℤ) (item : Item) (items : List Item) :
    adjust amount remaining.toNat (item :: items) =
      (adjust amount (remaining - 1).toNat items).orderedInsert ordered
        (if 0 < remaining then item else (item.1 - amount, item.2)) := by
  by_cases h : 0 < remaining
  · have hr : remaining.toNat = (remaining - 1).toNat + 1 := by omega
    rw [hr, adjust_cons_succ, ite_eq_left h]
  · have hr : remaining.toNat = 0 := by omega
    have hs : (remaining - 1).toNat = 0 := by omega
    rw [hr, hs, adjust_cons_zero, ite_eq_right h]

/-- Tail recursion retains the same upper-block subtraction precondition. -/
theorem drop_tail_condition (amount : ℕ) (remaining : ℤ) (item : Item) (items : List Item)
    (h : ∀ a ∈ (item :: items).drop remaining.toNat, amount ≤ a.1) :
    ∀ a ∈ items.drop (remaining - 1).toNat, amount ≤ a.1 := by
  by_cases hp : 0 < remaining
  · have hr : remaining.toNat = (remaining - 1).toNat + 1 := by omega
    simpa only [hr, List.drop_succ_cons] using h
  · have hr : remaining.toNat = 0 := by omega
    have ht : (remaining - 1).toNat = 0 := by omega
    intro a ha
    apply h a
    rw [hr, List.drop_zero]
    rw [ht, List.drop_zero] at ha
    exact List.mem_cons_of_mem item ha

/-- Once the lower block is exhausted, the current numerator admits subtraction. -/
theorem upper_head_bound (amount : ℕ) (remaining : ℤ) (item : Item) (items : List Item)
    (hp : ¬0 < remaining)
    (h : ∀ a ∈ (item :: items).drop remaining.toNat, amount ≤ a.1) : amount ≤ item.1 := by
  have hr : remaining.toNat = 0 := by omega
  apply h item
  rw [hr, List.drop_zero]
  exact List.mem_cons_self

end SampLib.SplittingPPS
