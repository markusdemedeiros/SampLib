import SampLib.Discrete.Laws.WeightedChoice
import SampLib.Uniform.Laws.RationalCoin

/-! # Expectation for uniform-envelope categorical rejection

A uniform proposal accepted with probability weight/envelope pays the categorical
credit on acceptance. The unused envelope funds an amplified retry.
-/

open MeasureTheory Finset
open scoped ENNReal NNReal

namespace SampLib.WeightedRejection

noncomputable section

/-- Unused portions of the category envelopes. -/
def spare (ws : List ℕ) (m : ℕ) : ℕ := (ws.map (m - ·)).sum

private theorem total_envelope (ws : List ℕ) (m : ℕ) (h : ∀ w ∈ ws, w ≤ m) :
    ws.sum + spare ws m = ws.length * m := by
  induction ws with
  | nil => simp [spare]
  | cons w ws IH =>
    have hw := h w (by simp)
    have ht := IH (fun x hx => h x (by simp [hx]))
    simp only [List.sum_cons, spare, List.map_cons, List.sum_cons, List.length_cons] at *
    nlinarith [Nat.sub_add_cancel hw]

/-- A bounded amplification factor, valid even when every proposal succeeds. -/
def factor (ws : List ℕ) (m : ℕ) : ℝ≥0 :=
  1 + (ws.length * m : ℝ≥0)⁻¹

/-- Continuation credits after the acceptance coin. -/
def coinCredit (ws : List ℕ) (m : ℕ) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞)
    (i : ℕ) (b : Bool) : ℝ≥0∞ :=
  if b then F i else (∫⁻ i, F i ∂WeightedChoice.law ws) + factor ws m * ε

/-- Credit for a uniform proposal, written directly with integer envelope widths. -/
def proposalCredit (ws : List ℕ) (m : ℕ) (F : ℕ → ℝ≥0∞)
    (ε : ℝ≥0∞) (i : ℕ) : ℝ≥0∞ :=
  (ws[i]?.getD 0 * F i + (m - ws[i]?.getD 0 : ℕ) *
    ((∫⁻ i, F i ∂WeightedChoice.law ws) + factor ws m * ε)) / m

private theorem sum_widths (ws : List ℕ) (m : ℕ) (F : ℕ → ℝ≥0∞) (R : ℝ≥0∞) :
    ∑ i ∈ range ws.length, ((ws[i]?.getD 0 : ℝ≥0∞) * F i +
      (m - ws[i]?.getD 0 : ℕ) * R) = WeightedChoice.weightedSum ws F + spare ws m * R := by
  induction ws generalizing F with
  | nil => simp [WeightedChoice.weightedSum, spare]
  | cons w ws IH =>
    rw [List.length_cons, sum_range_succ']
    simp only [List.getElem?_cons_zero, Option.getD_some, List.getElem?_cons_succ]
    rw [IH]
    simp only [WeightedChoice.weightedSum, spare, List.map_cons, List.sum_cons, Nat.cast_add]
    ring

/-- Accepted widths give categorical credit; unused widths fund the retry. -/
theorem expectation (ws : List ℕ) (m : ℕ) (hs : 0 < ws.sum) (hm : 0 < m)
    (hbound : ∀ w ∈ ws, w ≤ m) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∑ i ∈ range ws.length, proposalCredit ws m F ε i) / ws.length ≤
      (∫⁻ i, F i ∂WeightedChoice.law ws) + ε := by
  have htotal := total_envelope ws m hbound
  have hn := List.length_pos_of_sum_ne_zero ws hs.ne'
  have hd : (ws.length * m : ℝ≥0∞) ≠ 0 := by positivity
  have hdt : (ws.length * m : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by finiteness
  have hs0 : (ws.sum : ℝ≥0∞) ≠ 0 := by positivity
  have hsT : (ws.sum : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by finiteness
  let C := ∫⁻ i, F i ∂WeightedChoice.law ws
  have hw : WeightedChoice.weightedSum ws F = ws.sum * C := by
    dsimp [C]
    rw [WeightedChoice.lintegral_law, ENNReal.mul_div_cancel hs0 hsT]
  have hparts : (ws.sum : ℝ≥0∞) / (ws.length * m) +
      spare ws m / (ws.length * m) = 1 := by
    rw [ENNReal.div_add_div_same, ← Nat.cast_add, htotal, Nat.cast_mul,
      ENNReal.div_self hd hdt]
  have hamp : (spare ws m : ℝ≥0∞) / (ws.length * m) * factor ws m ≤ 1 := by
    rw [ENNReal.coe_nnreal_eq]
    have hD : (0 : ℝ) < ws.length * m := by positivity
    have hb : (spare ws m : ℝ) * (1 + ((ws.length : ℝ) * m)⁻¹) /
        (ws.length * m) ≤ 1 := by
      have ht : (ws.sum : ℝ) + spare ws m = (ws.length : ℝ) * m := by
        exact_mod_cast htotal
      have hp : (1 : ℝ) ≤ ws.sum := by exact_mod_cast hs
      rw [div_le_one hD]
      field_simp
      nlinarith
    have he : (spare ws m : ℝ≥0∞) / (ws.length * m) *
        ENNReal.ofReal (factor ws m : ℝ) =
        ENNReal.ofReal ((spare ws m : ℝ) * (1 + ((ws.length : ℝ) * m)⁻¹) /
          (ws.length * m)) := by
      rw [ENNReal.ofReal_div_of_pos hD,
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ spare ws m)]
      simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ws.length)]
      change _ = _ * ENNReal.ofReal (factor ws m : ℝ) / _
      rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
      ring
    rw [he]
    exact ENNReal.ofReal_le_one.mpr hb
  calc
    _ = ((ws.sum : ℝ≥0∞) / (ws.length * m) + spare ws m / (ws.length * m)) * C +
        (spare ws m / (ws.length * m) * (factor ws m : ℝ≥0∞)) * ε := by
      simp only [proposalCredit]
      rw [← ENNReal.sum_div, sum_widths, hw]
      simp only [ENNReal.div_eq_inv_mul]
      rw [ENNReal.mul_inv (Or.inl (by positivity : (ws.length : ℝ≥0∞) ≠ 0))
        (Or.inl (by finiteness : (ws.length : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)))]
      dsimp [C]
      ring
    _ ≤ C + ε := by
      rw [hparts, one_mul]
      exact add_le_add le_rfl (mul_le_of_le_one_left' hamp)

end

end SampLib.WeightedRejection

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
