module

public import Mathlib.Data.List.Sort
public import Mathlib.Algebra.BigOperators.Group.List.Basic

@[expose] public section

/-! # Integer states for Deville–Tillé splitting

The state stores one common denominator and a numerator for each labelled item.
Insertion sorting preserves labels and total mass while exposing the two split
boundaries. Rejected splits decrease the common integer denominator.
-/

namespace SampLib.SplittingPPS

abbrev Item := ℕ × ℤ

/-- The stable source ordering compares probability numerators only. -/
def ordered (a b : Item) : Prop := a.1 ≤ b.1

instance : DecidableRel ordered := fun _ _ => inferInstanceAs (Decidable (_ ≤ _))
instance : Std.Total ordered := ⟨fun a b => le_total a.1 b.1⟩
instance : IsTrans Item ordered := ⟨fun _ _ _ hab hbc => hab.trans hbc⟩

/-- Attach the input label and scale its prescribed inclusion probability. -/
def tag (count : ℕ) : List ℕ → ℤ → List Item
  | [], _ => []
  | w :: ws, label => (count * w, label) :: tag count ws (label + 1)

/-- Exact source preprocessing, using stable insertion into the sorted suffix. -/
def prepare (count : ℕ) (ws : List ℕ) (label : ℤ) : List Item :=
  (tag count ws label).insertionSort ordered

@[simp] theorem prepare_nil (count : ℕ) (label : ℤ) : prepare count [] label = [] := by
  simp only [prepare, tag, List.insertionSort_nil]

@[simp] theorem prepare_cons (count w : ℕ) (ws : List ℕ) (label : ℤ) :
    prepare count (w :: ws) label =
      (prepare count ws (label + 1)).orderedInsert ordered (count * w, label) := by
  simp only [prepare, tag, List.insertionSort_cons]

@[simp] theorem tag_length (count : ℕ) (ws : List ℕ) (label : ℤ) :
    (tag count ws label).length = ws.length := by
  induction ws generalizing label with
  | nil => rfl
  | cons w ws ih => simp only [tag, List.length_cons, ih]

/-- Preprocessing never creates or drops an item. -/
theorem prepare_perm (count : ℕ) (ws : List ℕ) (label : ℤ) :
    List.Perm (prepare count ws label) (tag count ws label) := List.perm_insertionSort ordered _

@[simp] theorem prepare_length (count : ℕ) (ws : List ℕ) (label : ℤ) :
    (prepare count ws label).length = ws.length := by
  rw [(prepare_perm count ws label).length_eq, tag_length]

/-- The probability boundaries are in increasing order, including ties. -/
theorem prepare_ordered (count : ℕ) (ws : List ℕ) (label : ℤ) :
    (prepare count ws label).Pairwise ordered := List.pairwise_insertionSort ordered _

/-- Initial total inclusion mass is sample size times population weight. -/
theorem prepare_mass (count : ℕ) (ws : List ℕ) (label : ℤ) :
    ((prepare count ws label).map Prod.fst).sum = count * ws.sum := by
  rw [((prepare_perm count ws label).map Prod.fst).sum_eq]
  induction ws generalizing label with
  | nil => simp [tag]
  | cons w ws ih => simp only [tag, List.map_cons, List.sum_cons, ih, Nat.mul_add]

/-- Subtract the split amount from the selected upper block. -/
def trim (amount cutoff : ℕ) (items : List Item) : List Item :=
  items.take cutoff ++ (items.drop cutoff).map (fun a => (a.1 - amount, a.2))

/-- Rejected splitting reorders the updated probabilities before the next step. -/
def adjust (amount cutoff : ℕ) (items : List Item) : List Item :=
  (trim amount cutoff items).insertionSort ordered

@[simp] theorem trim_length (amount cutoff : ℕ) (items : List Item) :
    (trim amount cutoff items).length = items.length := by
  simp only [trim, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

@[simp] theorem adjust_length (amount cutoff : ℕ) (items : List Item) :
    (adjust amount cutoff items).length = items.length := by
  simp [adjust]

private theorem subtract_mass (amount : ℕ) (items : List Item)
    (h : ∀ a ∈ items, amount ≤ a.1) :
    (items.map (fun a => a.1 - amount)).sum + amount * items.length =
      (items.map Prod.fst).sum := by
  induction items with
  | nil => simp
  | cons a items ih =>
    have ha := h a (by simp)
    have htail : ∀ a ∈ items, amount ≤ a.1 := fun a ha => h a (by simp [ha])
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
    have hrest := ih htail
    omega

/-- Subtraction preserves every item's residual numerator, including zero-probability items. -/
theorem adjust_mass (amount cutoff : ℕ) (items : List Item)
    (h : ∀ a ∈ items.drop cutoff, amount ≤ a.1) :
    ((adjust amount cutoff items).map Prod.fst).sum + amount * (items.drop cutoff).length =
      (items.map Prod.fst).sum := by
  rw [adjust, ((List.perm_insertionSort ordered (trim amount cutoff items)).map Prod.fst).sum_eq]
  have hsubtract := subtract_mass amount (items.drop cutoff) h
  have hparts := congrArg (fun xs : List Item => (xs.map Prod.fst).sum)
    (List.take_append_drop cutoff items)
  simp only [trim, List.map_append, List.sum_append, List.map_map, Function.comp_def]
  simp only [List.map_append, List.sum_append] at hparts
  omega

/-- The residual numerator total uses the correspondingly reduced common denominator. -/
theorem residual_mass (amount cutoff count denominator : ℕ) (items : List Item)
    (h : ∀ a ∈ items.drop cutoff, amount ≤ a.1)
    (hcount : (items.drop cutoff).length = count)
    (hmass : (items.map Prod.fst).sum = count * denominator) :
    ((adjust amount cutoff items).map Prod.fst).sum = count * (denominator - amount) := by
  have hsum := adjust_mass amount cutoff items h
  rw [hcount, hmass, Nat.mul_comm amount count] at hsum
  rw [Nat.mul_sub]
  omega

end SampLib.SplittingPPS
