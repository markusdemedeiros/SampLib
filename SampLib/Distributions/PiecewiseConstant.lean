import SampLib.Samplers.Histogram

/-! # Exact integer-grid masses of piecewise constant densities -/

open scoped ENNReal

namespace SampLib.PiecewiseConstant

noncomputable section

/-- A bin contributes its width times its constant nonnegative height. -/
def weights : List ℤ → List ℕ → List ℕ
  | a :: b :: xs, h :: hs => (b - a).toNat * h :: weights (b :: xs) hs
  | _, _ => []

/-- A finite partition with nonnegative heights; zero-height bins are allowed. -/
structure Model where
  points : List ℤ
  heights : List ℕ
  length : points.length = heights.length + 1
  increasing : ∀ i, i < heights.length → points[i]?.getD 0 < points[i + 1]?.getD 0
  positive : (weights points heights).sum ≠ 0

theorem weights_length (points : List ℤ) (heights : List ℕ)
    (hlen : points.length = heights.length + 1) :
    (weights points heights).length = heights.length := by
  induction heights generalizing points with
  | nil => cases points <;> simp [weights]
  | cons h hs IH =>
    match points with
    | a :: b :: xs => simp only [weights, List.length_cons]; rw [IH (b :: xs) (by simpa using hlen)]
    | [] => simp at hlen
    | [_] => simp at hlen

/-- Each categorical mass equals the number of grid cells times its density. -/
theorem weight_eq (points : List ℤ) (heights : List ℕ)
    (hlen : points.length = heights.length + 1) (i : ℕ) (hi : i < heights.length) :
    (weights points heights)[i]?.getD 0 =
      (points[i + 1]?.getD 0 - points[i]?.getD 0).toNat * heights[i]?.getD 0 := by
  induction heights generalizing points i with
  | nil => simp at hi
  | cons h hs IH =>
    match points with
    | a :: b :: xs =>
      cases i with
      | zero => simp [weights]
      | succ i =>
        simpa only [weights, List.getElem?_cons_succ, Nat.succ_eq_add_one] using
          IH (b :: xs) (by simpa using hlen) i (by simpa using hi)
    | [] => simp at hlen
    | [_] => simp at hlen

instance (D : Model) : NeZero (weights D.points D.heights).sum := ⟨D.positive⟩

theorem Model.partition_length (D : Model) :
    D.points.length = (weights D.points D.heights).length + 1 := by
  rw [weights_length _ _ D.length]
  exact D.length

theorem Model.bin_width (D : Model) (i : ℕ) (hi : i < (weights D.points D.heights).length) :
    D.points[i]?.getD 0 < D.points[i + 1]?.getD 0 :=
  D.increasing i (by simpa [weights_length _ _ D.length] using hi)

/-- Exact grid law: choose by width times height, then choose uniformly in that bin. -/
abbrev law (D : Model) := Histogram.law D.points (weights D.points D.heights)
  D.bin_width

/-- Computing bin areas and then conditioning on the selected bin preserves expectation. -/
theorem expectation (D : Model) (F : ℤ → ℝ≥0∞) :
    ∫⁻ i, ∫⁻ x, F x ∂Histogram.binLaw D.points (weights D.points D.heights) D.bin_width i
      ∂WeightedChoice.law (weights D.points D.heights) = ∫⁻ x, F x ∂law D :=
  Histogram.expectation D.points (weights D.points D.heights) D.bin_width F

end

end SampLib.PiecewiseConstant
