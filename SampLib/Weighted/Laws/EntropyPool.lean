import SampLib.Common.Laws.WordIntervals

/-! # Joint credit accounting for an entropy pool

A pool uniform on `0,…,width-1` splits into a rectangular accepted region and a
short rejected tail. In the rectangle, the remainder is the output and the
quotient remains in the pool. Their joint credit must be retained: a concrete
residual pool does not produce a conditionally fresh uniform next time.
-/

open Finset
open scoped ENNReal

namespace SampLib.EntropyPool

noncomputable section

/-- Quotient and remainder partition a uniform integer into independent rectangle coordinates. -/
theorem rectangle (bound copies : ℕ) (hb : 0 < bound) (F : ℕ → ℕ → ℝ≥0∞) :
    ∑ value ∈ range (bound * copies), F (value % bound) (value / bound) =
      ∑ quotient ∈ range copies, ∑ remainder ∈ range bound, F remainder quotient := by
  rw [WordIntervals.sum_blocks]
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro r hr
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (mem_range.mp hr), Nat.mul_add_div hb,
    Nat.div_eq_of_lt (mem_range.mp hr), Nat.add_zero]

/-- Acceptance keeps the unused quotient; rejection keeps exactly the short high tail. -/
theorem split (width bound : ℕ) (hb : 0 < bound) (F : ℕ → ℕ → ℝ≥0∞)
    (R : ℕ → ℝ≥0∞) :
    (∑ value ∈ range width,
      if value < bound * (width / bound) then F (value % bound) (value / bound)
      else R (value - bound * (width / bound))) =
      (∑ q ∈ range (width / bound), ∑ r ∈ range bound, F r q) +
        ∑ r ∈ range (width % bound), R r := by
  have hwidth : range width = range (bound * (width / bound) + width % bound) :=
    congrArg range (Nat.div_add_mod width bound).symm
  rw [hwidth, sum_range_add]
  have haccept :
      (∑ v ∈ range (bound * (width / bound)),
        if v < bound * (width / bound) then F (v % bound) (v / bound)
        else R (v - bound * (width / bound))) =
      ∑ q ∈ range (width / bound), ∑ r ∈ range bound, F r q := by
    calc
      _ = ∑ v ∈ range (bound * (width / bound)), F (v % bound) (v / bound) :=
        sum_congr rfl fun v hv => ite_eq_left (mem_range.mp hv)
      _ = _ := rectangle bound (width / bound) hb F
  rw [haccept]
  congr 1
  apply sum_congr rfl
  intro r hr
  rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]

/-- The same decomposition for normalized, possibly infinite continuation credits. -/
theorem expectation (width bound : ℕ) (hb : 0 < bound) (F : ℕ → ℕ → ℝ≥0∞)
    (R : ℕ → ℝ≥0∞) :
    (∑ value ∈ range width,
      if value < bound * (width / bound) then F (value % bound) (value / bound)
      else R (value - bound * (width / bound))) / width =
      ((∑ q ∈ range (width / bound), ∑ r ∈ range bound, F r q) +
        ∑ r ∈ range (width % bound), R r) / width := by
  rw [split width bound hb F R]

end

end SampLib.EntropyPool
