import SampLib.Distributions.Fenwick
import SampLib.Samplers.WeightedChoice

/-! # The categorical rank and its cumulative-mass interval -/

namespace SampLib.WeightedChoice

/-- The selected category is precisely the half-open cumulative interval containing the rank. -/
theorem category_interval (ws : List ℕ) (rank : ℕ) (hr : rank < ws.sum) :
    let q := category ws rank
    q < ws.length ∧ (ws.take q).sum ≤ rank ∧ rank < (ws.take (q + 1)).sum := by
  dsimp only
  induction ws generalizing rank with
  | nil => simp at hr
  | cons w ws IH =>
    simp only [List.sum_cons] at hr
    by_cases hw : rank < w
    · rw [category, ite_eq_left hw]
      simp [hw]
    · have htail : rank - w < ws.sum := by omega
      rcases IH (rank - w) htail with ⟨hindex, hlower, hupper⟩
      rw [category, ite_eq_right hw]
      simp only [List.length_cons, List.take_succ_cons, List.sum_cons]
      exact ⟨by omega, by omega, by omega⟩

end SampLib.WeightedChoice

namespace SampLib.FenwickCategory

/-- The bit-tree inversion and the canonical list-based categorical law use the same intervals. -/
theorem category_selects {n : ℕ} (w : Fin n → ℕ) (rank : ℕ)
    (hr : rank < (List.ofFn w).sum) :
    FenwickMath.Selects w rank (WeightedChoice.category (List.ofFn w) rank) := by
  simpa only [FenwickMath.Selects, FenwickMath.prefixSum_eq_take_sum, List.length_ofFn] using
    WeightedChoice.category_interval (List.ofFn w) rank hr

end SampLib.FenwickCategory
