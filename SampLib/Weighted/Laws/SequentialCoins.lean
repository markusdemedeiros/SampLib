import SampLib.Discrete.Laws.WeightedChoice
import SampLib.Uniform.Laws.RationalCoin
import SampLib.Common.Laws.Urn

/-! # Expectation for sequential conditional coins

Accepting the first category with its normalized weight, and otherwise renormalizing the
rest, preserves the categorical expectation.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.SequentialCoins

noncomputable section

/-- Categorical credit translated by the number of categories already visited. -/
def credit (ws : List ℕ) (offset : ℕ) (F : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ i, F (offset + i) ∂WeightedChoice.law ws

/-- Credit conditional on accepting or skipping the first category. -/
def continuation (ws : List ℕ) (offset : ℕ) (F : ℕ → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F offset else credit ws (offset + 1) F

/-- Renormalization of the remaining categories preserves the categorical expectation. -/
theorem expectation (w : ℕ) (ws : List ℕ) (hs : 0 < w + ws.sum)
    (offset : ℕ) (F : ℕ → ℝ≥0∞) :
    RealCoin.credit (Urn.bias w ws.sum) (continuation ws offset F) =
      credit (w :: ws) offset F := by
  rw [RealCoin.credit, Urn.pmf_true w ws.sum hs, Urn.pmf_false w ws.sum hs]
  simp only [continuation, ite_true, Bool.false_eq_true, ite_false]
  have hshift : (fun i => F (offset + (i + 1))) = fun i => F ((offset + 1) + i) := by
    funext i
    congr 1
    omega
  have hcons : credit (w :: ws) offset F =
      ((w : ℝ≥0∞) * F offset +
        WeightedChoice.weightedSum ws (fun i => F ((offset + 1) + i))) /
        ((w : ℝ≥0∞) + ws.sum) := by
    simp only [credit, WeightedChoice.lintegral_law, WeightedChoice.weightedSum,
      List.sum_cons, Nat.add_zero, Nat.cast_add, hshift]
  rw [hcons]
  have htail : WeightedChoice.weightedSum ws (fun i => F ((offset + 1) + i)) =
      ws.sum * credit ws (offset + 1) F := by
    by_cases hz : ws.sum = 0
    · rw [← WeightedChoice.rank_partition, hz]
      simp
    · rw [credit, WeightedChoice.lintegral_law,
        ENNReal.mul_div_cancel (by positivity) (by finiteness)]
  rw [htail]
  simp only [ENNReal.div_eq_inv_mul]
  ring

end

end SampLib.SequentialCoins
