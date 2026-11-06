import SampLib.Distributions.KnuthYaoCredits
import SampLib.PowerOfTwoCeiling

/-! # Padding and rejection credit for the fast loaded dice roller

Padding the total to a power of two adds a single rejection category. Its mass
is at most one half, so retries may double the auxiliary termination credit.
-/

open Finset
open scoped NNReal ENNReal

namespace SampLib.FastLoadedDiceCredits

noncomputable section

/-- The source appends this final outcome implicitly at the end of each column scan. -/
def augmented (ws : List ℕ) (P : ℕ) : List ℕ := ws ++ [P - ws.sum]

/-- Original categorical continuation credit. -/
def credit (ws : List ℕ) (F : ℕ → ℝ≥0∞) : ℝ≥0∞ := WeightedChoice.weightedSum ws F / ws.sum

/-- The padded category restarts with the same continuation and doubled termination credit. -/
def extended (ws : List ℕ) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (i : ℕ) : ℝ≥0∞ :=
  if i < ws.length then F i else credit ws F + 2 * ε

theorem weightedSum_congr (ws : List ℕ) (F G : ℕ → ℝ≥0∞)
    (h : ∀ i, i < ws.length → F i = G i) :
    WeightedChoice.weightedSum ws F = WeightedChoice.weightedSum ws G := by
  induction ws generalizing F G with
  | nil => rfl
  | cons w ws ih =>
    simp only [WeightedChoice.weightedSum]
    rw [h 0 (by simp), ih (fun i => F (i + 1)) (fun i => G (i + 1))
      (fun i hi => h (i + 1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hi))]

theorem weightedSum_append (ws vs : List ℕ) (F : ℕ → ℝ≥0∞) :
    WeightedChoice.weightedSum (ws ++ vs) F = WeightedChoice.weightedSum ws F +
      WeightedChoice.weightedSum vs (fun i => F (ws.length + i)) := by
  induction ws generalizing F with
  | nil => simp [WeightedChoice.weightedSum]
  | cons w ws ih =>
    simp only [List.cons_append, WeightedChoice.weightedSum, ih, List.length_cons]
    simp only [add_assoc, add_comm]

theorem augmented_sum (ws : List ℕ) (P : ℕ) (hP : ws.sum ≤ P) :
    (augmented ws P).sum = P := by simp only [augmented, List.sum_append, List.sum_singleton]; omega

theorem augmented_weightedSum (ws : List ℕ) (P : ℕ) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    WeightedChoice.weightedSum (augmented ws P) (extended ws F ε) =
      WeightedChoice.weightedSum ws F + (P - ws.sum : ℕ) * (credit ws F + 2 * ε) := by
  rw [augmented, weightedSum_append]
  rw [weightedSum_congr ws (extended ws F ε) F
    (fun i hi => ite_eq_left hi)]
  simp [WeightedChoice.weightedSum, extended]

/-- Padding preserves every continuation credit, and rejection pays for at most one ε. -/
theorem expectation (ws : List ℕ) (P : ℕ) (hT : 0 < ws.sum)
    (hP : ws.sum ≤ P) (hdouble : P ≤ 2 * ws.sum) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    WeightedChoice.weightedSum (augmented ws P) (extended ws F ε) / P ≤ credit ws F + ε := by
  have hP0 : (P : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (hT.trans_le hP)
  have hT0 : (ws.sum : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hT
  have hsum : WeightedChoice.weightedSum ws F = (ws.sum : ℝ≥0∞) * credit ws F := by
    simpa only [credit, mul_comm] using
      (ENNReal.div_mul_cancel hT0 (by finiteness)
        (b := WeightedChoice.weightedSum ws F)).symm
  have hpadded : (P : ℝ≥0∞) = ws.sum + (P - ws.sum : ℕ) := by
    exact_mod_cast (Nat.add_sub_of_le hP).symm
  have haux : (2 : ℝ≥0∞) * (P - ws.sum : ℕ) ≤ P := by
    exact_mod_cast (show 2 * (P - ws.sum) ≤ P by omega)
  rw [augmented_weightedSum]
  apply (ENNReal.div_le_iff hP0 (by finiteness)).mpr
  rw [hsum]
  calc
    _ = (ws.sum + (P - ws.sum : ℕ) : ℝ≥0∞) * credit ws F +
        (2 * (P - ws.sum : ℕ) : ℝ≥0∞) * ε := by ring
    _ ≤ (P : ℝ≥0∞) * credit ws F + P * ε := by
      rw [← hpadded]
      simpa only [mul_comm, add_comm] using
        add_le_add_left (mul_le_mul_right haux ε) ((P : ℝ≥0∞) * credit ws F)
    _ = (credit ws F + ε) * P := by ring

end

end SampLib.FastLoadedDiceCredits
