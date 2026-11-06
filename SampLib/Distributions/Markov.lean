import SampLib.Distributions.FiniteKernels
import SampLib.Distributions.WeightedSupport

/-! # Finite stochastic matrices with integer weights -/

open scoped ENNReal

namespace SampLib.MarkovChain

noncomputable section

/-- A nonnegative integer row with positive total. -/
abbrev Row := {ws : List ℕ // 0 < ws.sum}

private def defaultRow : Row := ⟨[1], by decide⟩

/-- Total lookup, with an arbitrary stochastic row outside the state space. -/
def row (rows : List Row) (i : ℕ) : Row := rows[i]?.getD defaultRow

theorem row_get (rows : List Row) (i : ℕ) (hi : i < rows.length) :
    row rows i = rows.get ⟨i, hi⟩ := by
  simp [row, List.getElem?_eq_getElem hi]

section mathematics

open MeasureTheory

/-- Normalize each row independently. -/
def kernel (rows : List Row) (i : ℕ) : Measure ℕ := WeightedChoice.law (row rows i).val

instance (rows : List Row) (i : ℕ) : IsProbabilityMeasure (kernel rows i) := by
  let : NeZero (row rows i).val.sum := ⟨(row rows i).property.ne'⟩
  exact inferInstanceAs (IsProbabilityMeasure (WeightedChoice.law (row rows i).val))

abbrev law (rows : List Row) := FiniteKernels.iterate (kernel rows)

/-- A square transition matrix cannot leave its finite state space. -/
theorem kernel_support (rows : List Row)
    (hsquare : ∀ r ∈ rows, r.val.length = rows.length) (i : ℕ) (hi : i < rows.length) :
    ∀ᵐ j ∂kernel rows i, j < rows.length := by
  have hlen : (row rows i).val.length = rows.length := by
    rw [row_get rows i hi]
    exact hsquare _ (List.get_mem ..)
  simpa only [kernel, hlen] using WeightedChoice.ae_lt_length (row rows i).val

end mathematics

end

end SampLib.MarkovChain
