module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public meta import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The running maximum of a natural-weight vector -/

namespace SampLib.WeightMaximum

def maximum (ws : List ℕ) (current : ℕ) : ℕ := ws.foldl max current

@[simp] theorem maximum_nil (current : ℕ) : maximum [] current = current := rfl

@[simp] theorem maximum_cons (w : ℕ) (ws : List ℕ) (current : ℕ) :
    maximum (w :: ws) current = maximum ws (max current w) := rfl

/-- The final maximum bounds both the initial accumulator and every input weight. -/
theorem bounds (ws : List ℕ) (current : ℕ) :
    current ≤ maximum ws current ∧ ∀ w ∈ ws, w ≤ maximum ws current := by
  induction ws generalizing current with
  | nil => simp
  | cons w ws ih =>
    obtain ⟨hcurrent, htail⟩ := ih (max current w)
    rw [maximum_cons]
    refine ⟨(le_max_left current w).trans hcurrent, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (le_max_right current x).trans hcurrent
    · exact htail x hx

/-- Positive total mass guarantees a positive rejection envelope. -/
theorem positive (ws : List ℕ) (ht : 0 < ws.sum) : 0 < maximum ws 0 := by
  by_contra h
  have hzero : maximum ws 0 = 0 := by omega
  have hsum : ws.sum = 0 := by
    apply List.sum_eq_zero
    intro w hw
    have hbound := (bounds ws 0).2 w hw
    omega
  omega

end SampLib.WeightMaximum
