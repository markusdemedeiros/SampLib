import SampLib.Constants.Laws.ApproximateDigits

open SampLib MeasureTheory FromApproximateDigits
open scoped ENNReal

noncomputable section

private def zeroBelow : Model where
  base := 2
  atLeastTwo := by decide
  probability := 0
  approximation := fun _ => -1
  accurate := by intro n; simp

private def zeroAbove : Model where
  base := 2
  atLeastTwo := by decide
  probability := 0
  approximation := fun _ => 1
  accurate := by intro n; simp

private def oneAbove : Model where
  base := 2
  atLeastTwo := by decide
  probability := 1
  approximation := fun n => (2 : ℤ) ^ (n + 1) + 1
  accurate := by
    intro n
    simp only [Int.cast_add, Int.cast_pow, Int.cast_ofNat, Set.Icc.coe_one, one_mul]
    norm_num

-- Both first digits retry at a legal endpoint; one-step contraction is unavailable.
example (j : Fin 2) :
    ¬zeroAbove.approximation 0 + 1 ≤ (j : ℤ) ∧
      ¬(j : ℤ) ≤ zeroAbove.approximation 0 - 2 := by
  have hj := j.isLt
  change ¬(1 : ℤ) + 1 ≤ j ∧ ¬(j : ℤ) ≤ 1 - 2
  omega

example : (zeroBelow.enclosure 0).lower = -2 := rfl
example : (oneAbove.enclosure 0).upper = 4 := by decide

example (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    RadixPosterior.credit 1 0 F =
      (RadixPosterior.credit 3 0 F + RadixPosterior.credit 3 1 F +
        RadixPosterior.credit 3 2 F) / 3 := by
  simpa [Finset.sum_range_succ] using
    RadixPosterior.credit_split 1 (by decide) 3 (by decide) 0 F hF

example (d : ℕ) (c : ℤ) : RadixPosterior.credit d c (fun _ => ∞) = ∞ := by
  simp [RadixPosterior.credit]

example (F : Bool → ℝ≥0∞) : 1 ≤ zeroAbove.credit 0 F 1 0 :=
  zeroAbove.unresolved_credit 0 0 F (by decide) (by decide)

#print axioms RadixPosterior.credit_split
#print axioms Model.expectation
#print axioms Model.exists_horizon
#print axioms Model.unresolved_credit
