import SampLib.Weighted.Laws.OptimalMatrixData

/-! # Restart credit for the optional cyclic-matrix rejection row

Padding changes only the final outcome. Its probability is at most one half,
so doubling auxiliary credit on rejection pays at most one credit in expectation.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.OptimalMatrix

noncomputable section

private theorem weightedSum_congr (ws : List ℕ) (F G : ℕ → ℝ≥0∞)
    (h : ∀ i, i < ws.length → F i = G i) :
    WeightedChoice.weightedSum ws F = WeightedChoice.weightedSum ws G := by
  induction ws generalizing F G with
  | nil => rfl
  | cons w ws ih =>
    rw [WeightedChoice.weightedSum, WeightedChoice.weightedSum,
      h 0 (by simp), ih (fun i => F (i + 1)) (fun i => G (i + 1))
        (fun i hi => h (i + 1) (by simpa using Nat.succ_lt_succ hi))]

private theorem weightedSum_append (xs ys : List ℕ) (F : ℕ → ℝ≥0∞) :
    WeightedChoice.weightedSum (xs ++ ys) F = WeightedChoice.weightedSum xs F +
      WeightedChoice.weightedSum ys (fun i => F (xs.length + i)) := by
  induction xs generalizing F with
  | nil => simp [WeightedChoice.weightedSum]
  | cons w xs ih =>
    simp only [List.cons_append, WeightedChoice.weightedSum, List.length_cons]
    rw [ih]
    have hshift : (fun i => F (xs.length + i + 1)) =
        fun i => F (xs.length + 1 + i) := by funext i; congr 1; omega
    rw [hshift, add_assoc]

private theorem padded_credit (ws : List ℕ) (D : ℕ) (F : ℕ → ℝ≥0∞) (G : ℝ≥0∞) :
    WeightedChoice.weightedSum (values ws D)
      (OptimalCyclic.leafCredit (rejectionIndex ws D) G F) =
      WeightedChoice.weightedSum ws F + (D - ws.sum : ℕ) * G := by
  unfold values rejectionIndex
  by_cases hr : D - ws.sum = 0
  · simp only [hr, ite_true, Nat.cast_zero, zero_mul, add_zero]
    apply weightedSum_congr
    intro i _
    exact ite_eq_right (by omega : ¬(i : ℤ) = -1)
  · simp only [hr, ite_false, weightedSum_append]
    have hp : WeightedChoice.weightedSum ws
        (OptimalCyclic.leafCredit (ws.length : ℤ) G F) = WeightedChoice.weightedSum ws F := by
      apply weightedSum_congr
      intro i hi
      exact ite_eq_right (by exact_mod_cast (Nat.ne_of_lt hi) : ¬(i : ℤ) = ws.length)
    rw [hp]
    simp [WeightedChoice.weightedSum, OptimalCyclic.leafCredit]

/-- The exact padded row law pays the caller's continuation and one auxiliary credit. -/
theorem expectation (ws : List ℕ) (D : ℕ) (hs : 0 < ws.sum) (hD : ws.sum ≤ D)
    (hupper : D ≤ 2 * ws.sum) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    WeightedChoice.weightedSum (values ws D)
      (OptimalCyclic.leafCredit (rejectionIndex ws D)
        ((∫⁻ i, F i ∂WeightedChoice.law ws) + 2 * ε) F) / D ≤
      (∫⁻ i, F i ∂WeightedChoice.law ws) + ε := by
  let C := ∫⁻ i, F i ∂WeightedChoice.law ws
  have hpos : 0 < D := hs.trans_le hD
  have hD0 : (D : ℝ≥0∞) ≠ 0 := by exact_mod_cast hpos.ne'
  have hDtop : (D : ℝ≥0∞) ≠ ∞ := by finiteness
  have hcredit : WeightedChoice.weightedSum ws F = (ws.sum : ℝ≥0∞) * C := by
    dsimp [C]
    rw [WeightedChoice.lintegral_law,
      ENNReal.mul_div_cancel (by exact_mod_cast hs.ne') (by finiteness)]
  have hparts : ((ws.sum : ℝ≥0∞) + (D - ws.sum : ℕ)) / D = 1 := by
    rw [← Nat.cast_add, Nat.add_sub_of_le hD, ENNReal.div_self hD0 hDtop]
  have hretry : ((2 * (D - ws.sum) : ℕ) : ℝ≥0∞) / D ≤ 1 := by
    rw [ENNReal.div_le_iff hD0 hDtop, one_mul]
    exact_mod_cast (show 2 * (D - ws.sum) ≤ D by omega)
  calc
    _ = (((ws.sum : ℝ≥0∞) + (D - ws.sum : ℕ)) / D) * C +
        (((2 * (D - ws.sum) : ℕ) : ℝ≥0∞) / D) * ε := by
      rw [padded_credit, hcredit]
      simp only [Nat.cast_mul, Nat.cast_ofNat, ENNReal.div_eq_inv_mul]
      ring
    _ ≤ C + ε := by
      rw [hparts, one_mul]
      exact add_le_add le_rfl (mul_le_of_le_one_left' hretry)

/-- The actual encoded matrix pays its continuation and the outer retry credit. -/
theorem restart_expectation (ws : List ℕ) {k l : ℕ} (hl : l < k) (hs : 0 < ws.sum)
    (hD : ws.sum ≤ OptimalEncoding.denominator k l)
    (hupper : OptimalEncoding.denominator k l ≤ 2 * ws.sum)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    OptimalCyclic.rowCredit (encoded ws k l) k l 0
      (OptimalCyclic.leafCredit (rejectionIndex ws (OptimalEncoding.denominator k l))
        ((∫⁻ i, F i ∂WeightedChoice.law ws) + 2 * ε) F) ≤
      (∫⁻ i, F i ∂WeightedChoice.law ws) + ε := by
  rw [encoded_row_credit ws hl hD]
  exact expectation ws _ hs hD hupper F ε

end

end SampLib.OptimalMatrix
