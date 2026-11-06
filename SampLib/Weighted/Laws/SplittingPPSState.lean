module

public import SampLib.Weighted.Laws.SplittingPPSBounds

@[expose] public section

/-! # Valid integer states for splitting PPS

Numerators have total `count * denominator`. The interior split exposes one
non-saturated lower boundary and one positive upper boundary. Rejection reduces
both the numerators and the common denominator, preserving this invariant.
-/

namespace SampLib.SplittingPPS

structure State (size count : ℕ) where
  items : List Item
  denominator : ℕ
  length_eq : items.length = size
  positive : 0 < denominator
  ordered : items.Pairwise SplittingPPS.ordered
  bounded : ∀ a ∈ items, a.1 ≤ denominator
  mass : (items.map Prod.fst).sum = count * denominator

namespace State

variable {size count : ℕ}

/-- Source lookup conventions are total; interior bounds justify both positions. -/
def low (s : State size count) : ℕ := (s.items[size - count - 1]?.getD (0, 0)).1

def high (s : State size count) : ℕ := (s.items[size - count]?.getD (0, 0)).1

def amount (s : State size count) : ℕ := min (s.denominator - s.low) s.high

/-- The deterministic accepting branch selects the upper `count` labels. -/
def topLabels (s : State size count) : List ℤ :=
  (s.items.drop (size - count)).map Prod.snd

theorem boundaries (s : State size count) (hc : 0 < count) (hs : count < size) :
    s.low < s.denominator ∧ 0 < s.high := by
  have hlen : s.items.length = size - count + count := by rw [s.length_eq]; omega
  have h := interior_boundaries s.items (size - count) count s.denominator
    (by omega) hc hlen s.positive s.ordered s.bounded s.mass
  have hlo : size - count - 1 < s.items.length := by rw [s.length_eq]; omega
  have hhi : size - count < s.items.length := by rw [s.length_eq]; omega
  simpa only [low, high, List.getElem?_eq_getElem hlo, List.getElem?_eq_getElem hhi,
    Option.getD_some] using h

/-- A rejected interior split strictly decreases the natural denominator. -/
theorem amount_bounds (s : State size count) (hc : 0 < count) (hs : count < size) :
    0 < s.amount ∧ s.amount ≤ s.denominator ∧ s.denominator - s.amount < s.denominator :=
  split_amount_bounds s.denominator s.low s.high (s.boundaries hc hs).1
    (s.boundaries hc hs).2

theorem amount_le_top (s : State size count) (hc : 0 < count) (hs : count < size) :
    ∀ a ∈ s.items.drop (size - count), s.amount ≤ a.1 := by
  have hcut : size - count < s.items.length := by rw [s.length_eq]; omega
  have h := boundary_le_top s.items (size - count) hcut s.ordered
  have hhi : s.high = (s.items[size - count]'hcut).1 := by
    simp only [high, List.getElem?_eq_getElem hcut, Option.getD_some]
  intro a ha
  exact (min_le_right (s.denominator - s.low) s.high).trans (hhi.trans_le (h a ha))

theorem topLabels_length (s : State size count) (hc : count ≤ size) :
    s.topLabels.length = count := by
  simp only [topLabels, List.length_map, List.length_drop, s.length_eq]
  omega

/-- Every residual numerator fits the reduced denominator, including the terminal zero state. -/
theorem adjusted_bounded (s : State size count) (hc : 0 < count) (hs : count < size) :
    ∀ a ∈ adjust s.amount (size - count) s.items, a.1 ≤ s.denominator - s.amount := by
  have hlo : size - count - 1 < s.items.length := by rw [s.length_eq]; omega
  apply adjust_bounded s.items (size - count) s.denominator s.amount
    (by omega) (by rw [s.length_eq]; omega) s.ordered s.bounded
  have hlow : s.low = (s.items[size - count - 1]'hlo).1 := by
    simp only [low, List.getElem?_eq_getElem hlo, Option.getD_some]
  simpa only [amount, hlow] using min_le_left (s.denominator - s.low) s.high

/-- The residual state exists precisely when rejection has positive probability. -/
def next (s : State size count) (hc : 0 < count) (hs : count < size)
    (hnext : s.amount < s.denominator) : State size count where
  items := adjust s.amount (size - count) s.items
  denominator := s.denominator - s.amount
  length_eq := by rw [adjust_length, s.length_eq]
  positive := Nat.sub_pos_of_lt hnext
  ordered := adjust_ordered _ _ _
  bounded := s.adjusted_bounded hc hs
  mass := residual_mass s.amount (size - count) count s.denominator s.items
    (s.amount_le_top hc hs) (by simp only [List.length_drop, s.length_eq]; omega) s.mass

@[simp] theorem next_denominator (s : State size count) (hc : 0 < count)
    (hs : count < size) (hnext : s.amount < s.denominator) :
    (s.next hc hs hnext).denominator = s.denominator - s.amount := rfl

theorem next_lt (s : State size count) (hc : 0 < count) (hs : count < size)
    (hnext : s.amount < s.denominator) :
    (s.next hc hs hnext).denominator < s.denominator := (s.amount_bounds hc hs).2.2

theorem next_labels (s : State size count) (hc : 0 < count) (hs : count < size)
    (hnext : s.amount < s.denominator) :
    ((s.next hc hs hnext).items.map Prod.snd).Perm (s.items.map Prod.snd) :=
  adjust_labels _ _ _

theorem tag_bounded (ws : List ℕ) (count total : ℕ) (label : ℤ)
    (hcap : ∀ w ∈ ws, count * w ≤ total) : ∀ a ∈ tag count ws label, a.1 ≤ total := by
  induction ws generalizing label with
  | nil => simp [tag]
  | cons w ws ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hcap w (by simp)
    · exact ih (label + 1) (fun x hx => hcap x (by simp [hx])) a ha

/-- Stable preprocessing yields the initial state for every admissible positive-total population. -/
def initial (ws : List ℕ) (count : ℕ) (ht : 0 < ws.sum)
    (hcap : ∀ w ∈ ws, count * w ≤ ws.sum) : State ws.length count where
  items := prepare count ws 0
  denominator := ws.sum
  length_eq := prepare_length _ _ _
  positive := ht
  ordered := prepare_ordered _ _ _
  bounded := fun a ha => tag_bounded ws count ws.sum 0 hcap a ((prepare_perm _ _ _).mem_iff.mp ha)
  mass := prepare_mass _ _ _

end State

end SampLib.SplittingPPS
