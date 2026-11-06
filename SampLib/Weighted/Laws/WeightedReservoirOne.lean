import SampLib.Discrete.Laws.WeightedChoice
import SampLib.Uniform.Laws.RationalCoin
import SampLib.Common.Laws.Urn

/-! # Expectation for one-item weighted reservoirs

The previously selected label stands for one virtual item that carries all earlier
weight. Each arriving item competes with it by its own weight.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.WeightedReservoirOne

noncomputable section

/-- The ordinary categorical law, with integer labels. -/
def law (ws : List ℕ) : Measure ℤ := (WeightedChoice.law ws).map (fun i : ℕ => (i : ℤ))

instance (ws : List ℕ) [NeZero ws.sum] : IsProbabilityMeasure (law ws) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

theorem lintegral_law (ws : List ℕ) (F : ℤ → ℝ≥0∞) :
    ∫⁻ i, F i ∂law ws =
      WeightedChoice.weightedSum ws (fun i => F (i : ℤ)) / ws.sum := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    WeightedChoice.lintegral_law]

/-- Credit for the old virtual item and the not-yet-visited labels. -/
def credit (total : ℕ) (selected : ℤ) (ws : List ℕ) (offset : ℕ)
    (F : ℤ → ℝ≥0∞) : ℝ≥0∞ :=
  (total * F selected + WeightedChoice.weightedSum ws (fun i => F ((offset + i : ℕ) : ℤ))) /
    (total + ws.sum : ℕ)

/-- Conditional credit after the arriving item competes with the old reservoir. -/
def continuation (total w : ℕ) (selected : ℤ) (ws : List ℕ) (offset : ℕ)
    (F : ℤ → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  credit (total + w) (if b then (offset : ℤ) else selected) ws (offset + 1) F

private theorem next_index (offset i : ℕ) :
    ((offset + (i + 1) : ℕ) : ℤ) = ((offset + 1 + i : ℕ) : ℤ) := by omega

/-- Replacement conserves each label's weight, including arbitrary infinite credits. -/
theorem expectation (total w : ℕ) (selected : ℤ) (ws : List ℕ) (offset : ℕ)
    (hp : 0 < total + w) (F : ℤ → ℝ≥0∞) :
    RealCoin.credit (Urn.bias w total) (continuation total w selected ws offset F) =
      credit total selected (w :: ws) offset F := by
  have hp' : 0 < w + total := by omega
  rw [RealCoin.credit, Urn.pmf_true w total hp', Urn.pmf_false w total hp']
  simp only [continuation, ite_true, Bool.false_eq_true, ite_false]
  have hinv : ((w : ℝ≥0∞) + total)⁻¹ * ((w : ℝ≥0∞) + total) = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast (Nat.ne_of_gt hp')) (by finiteness)
  calc
    _ = (((w : ℝ≥0∞) + total)⁻¹ * ((w : ℝ≥0∞) + total)) *
        credit total selected (w :: ws) offset F := by
      have hshift : (fun i => F ((offset + (i + 1) : ℕ) : ℤ)) =
          fun i => F ((offset + 1 + i : ℕ) : ℤ) := by
        funext i
        congr 1
        omega
      simp only [credit, WeightedChoice.weightedSum, List.sum_cons, Nat.add_zero]
      rw [hshift]
      simp only [Nat.cast_add, add_assoc, ENNReal.div_eq_inv_mul]
      ring
    _ = _ := by rw [hinv, one_mul]

/-- A zero-weight arrival leaves the virtual population unchanged. -/
theorem zero_step (total w : ℕ) (selected : ℤ) (ws : List ℕ) (offset : ℕ)
    (hz : total + w = 0) (F : ℤ → ℝ≥0∞) :
    credit total selected (w :: ws) offset F = credit (total + w) selected ws (offset + 1) F := by
  have hprefix : total = 0 := by omega
  have hw : w = 0 := by omega
  subst total w
  simp only [credit, WeightedChoice.weightedSum, List.sum_cons, Nat.add_zero,
    Nat.cast_zero, zero_mul, zero_add, next_index]

/-- No remaining items means the virtual item retains the entire distribution. -/
theorem credit_nil (total : ℕ) (selected : ℤ) (hp : 0 < total) (offset : ℕ)
    (F : ℤ → ℝ≥0∞) : credit total selected [] offset F = F selected := by
  simp only [credit, WeightedChoice.weightedSum, List.sum_nil, add_zero,
    ENNReal.div_eq_inv_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel (by positivity) (by finiteness), one_mul]

/-- The zero-weight sentinel disappears even when its continuation credit is infinite. -/
theorem initial_credit (ws : List ℕ) (F : ℤ → ℝ≥0∞) :
    credit 0 (-1) ws 0 F = ∫⁻ i, F i ∂law ws := by
  rw [lintegral_law]
  simp only [credit, Nat.cast_zero, zero_mul, zero_add]

end

end SampLib.WeightedReservoirOne
