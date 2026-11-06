module

public import SampLib.Distributions.LatentReal.ReciprocalSelection

@[expose] public section

/-! The selector is total, least, and measurable even on worlds with no separating interval. -/

open Set MeasureTheory

namespace SampLib.LatentReal.ReciprocalSelection.ProducerCallers

noncomputable section

def zeroInterval : RationalInterval := RationalInterval.point 0 1 (by norm_num)
def oneInterval : RationalInterval := RationalInterval.point 1 1 (by norm_num)

example (n : ℕ) : precision (fun _ _ : ℕ => zeroInterval) n 0 = n := by
  apply precision_of_none
  simp [separated, zeroInterval, RationalInterval.point]

example (n : ℕ) : precision (fun _ _ : ℕ => oneInterval) n 0 = n := by
  apply le_antisymm
  · apply precision_min _ n 0 le_rfl
    simp [separated, oneInterval, RationalInterval.point]
  · exact precision_ge _ n 0

/-- The world chooses the first separating index, independently of the requested lower bound. -/
def delayed (k ω : ℕ) : RationalInterval := if k < ω then zeroInterval else oneInterval

theorem separated_delayed (k ω : ℕ) : separated (delayed k ω) ↔ ω ≤ k := by
  by_cases h : k < ω
  · simp [delayed, h, separated, zeroInterval, RationalInterval.point, Nat.not_le.mpr h]
  · simp [delayed, h, separated, oneInterval, RationalInterval.point, Nat.le_of_not_gt h]

theorem precision_delayed (n ω : ℕ) : precision delayed n ω = max n ω := by
  have hsep := (separated_delayed (max n ω) ω).mpr (le_max_right n ω)
  apply le_antisymm
  · exact precision_min delayed n ω (le_max_left n ω) hsep
  · exact max_le (precision_ge delayed n ω) ((separated_delayed _ _).mp
      (precision_separated delayed n ω ⟨max n ω, le_max_left n ω, hsep⟩))

example (n : ℕ) : Measurable (precision delayed n) :=
  measurable_precision delayed (fun _ => measurable_from_nat) (fun _ => measurable_from_nat) n

example (n : ℕ) : Measurable (fun ω => (delayed (precision delayed n ω) ω).denominator) :=
  measurable_selected delayed (fun _ => measurable_from_nat) (fun _ => measurable_from_nat)
    (fun k ω => (delayed k ω).denominator) (fun _ => measurable_from_nat) n

#print axioms precision_spec
#print axioms precision_of_none
#print axioms measurable_precision
#print axioms measurable_selected
#print axioms precision_separated_of_approximates
#print axioms precision_delayed

end

end SampLib.LatentReal.ReciprocalSelection.ProducerCallers
