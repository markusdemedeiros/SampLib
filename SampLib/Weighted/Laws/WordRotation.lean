import SampLib.Common.Laws.WordIntervals

/-! # Rotating complete residue cycles

Discarding an incomplete low interval leaves complete cycles, merely rotated.
The proof never cancels continuation credits, which may be infinite.
-/

open Finset
open scoped ENNReal

namespace SampLib.WordRotation

noncomputable section

theorem sum_cycle (width offset : ℕ) (F : ℕ → ℝ≥0∞) :
    ∑ j ∈ range width, F ((offset + j) % width) = ∑ j ∈ range width, F j := by
  induction offset with
  | zero =>
    exact sum_congr rfl fun j hj => by
      simp only [Nat.zero_add, Nat.mod_eq_of_lt (mem_range.mp hj)]
  | succ offset ih =>
    cases width with
    | zero => simp
    | succ width =>
      calc
        _ = (∑ j ∈ range width, F ((offset + (j + 1)) % (width + 1))) +
            F (offset % (width + 1)) := by
          rw [sum_range_succ]
          simp only [Nat.add_right_comm offset 1,
            Nat.add_assoc, Nat.add_mod_right]
        _ = ∑ j ∈ range (width + 1), F ((offset + j) % (width + 1)) := by
          simp only [sum_range_succ', Nat.add_zero, add_comm]
        _ = _ := ih

theorem sum_cycles (width copies offset : ℕ) (F : ℕ → ℝ≥0∞) :
    ∑ k ∈ range (width * copies), F ((offset + k) % width) =
      copies * ∑ j ∈ range width, F j := by
  rw [WordIntervals.sum_blocks]
  have hblock (i : ℕ) :
      ∑ j ∈ range width, F ((offset + (width * i + j)) % width) =
        ∑ j ∈ range width, F j := by
    simpa only [Nat.add_left_comm offset (width * i), Nat.mul_add_mod] using
      sum_cycle width offset F
  simp_rw [hblock]
  simp [nsmul_eq_mul]

end

end SampLib.WordRotation
