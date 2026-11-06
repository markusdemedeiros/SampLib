import SampLib.Samplers.WeightedRejection

/-! # Reusable continuation credits for uniform-envelope categorical rejection -/

open MeasureTheory
open scoped ENNReal NNReal

namespace SampLib.EnvelopeRejection

open WeightedRejection

noncomputable section

/-- A positive finite envelope supports strict retry-credit amplification. -/
theorem one_lt_factor (ws : List ℕ) (m : ℕ) (hn : 0 < ws.length) (hm : 0 < m) :
    1 < factor ws m := by
  apply lt_add_of_pos_right
  exact inv_pos.mpr (by positivity)

/-- The rational acceptance coin pays the exact weight and unused-envelope credits. -/
theorem coin_expectation (ws : List ℕ) (m : ℕ) (hm : 0 < m)
    (hbound : ∀ w ∈ ws, w ≤ m) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (i : Fin ws.length) :
    RealCoin.credit
      (RationalCoin.bias (ws.get i) m (by positivity) (by exact_mod_cast hm)
        (by exact_mod_cast hbound _ (List.get_mem ..))) (coinCredit ws m F ε i) =
      proposalCredit ws m F ε i := by
  have hw : ws.get i ≤ m := hbound _ (List.get_mem ..)
  have hmR : (0 : ℝ) < m := by positivity
  have hc : 1 - (ws.get i : ℝ) / m = ((m - ws.get i : ℕ) : ℝ) / m := by
    rw [Nat.cast_sub hw]
    field_simp
  simp only [RealCoin.credit, RealCoin.pmf, RationalCoin.bias, coinCredit,
    Bool.false_eq_true, ite_true, ite_false, proposalCredit, Int.cast_natCast]
  rw [hc, List.get_eq_getElem]
  simp only [List.getElem?_eq_getElem i.isLt, Option.getD_some]
  rw [ENNReal.ofReal_div_of_pos hmR, ENNReal.ofReal_div_of_pos hmR]
  simp only [ENNReal.ofReal_natCast, ENNReal.div_eq_inv_mul]
  ring

end

end SampLib.EnvelopeRejection
