module

public import SampLib.Weighted.Laws.SplittingPPSBounds
public import Mathlib.Basic.ENNReal.Inv

@[expose] public section

/-! # Prescribed inclusion credits under splitting

The selected upper block removes the same integer amount from each numerator.
Its credit and the residual credit sum to the original credit, even at infinity.
-/

open scoped ENNReal

namespace SampLib.SplittingPPS

noncomputable section

/-- Unnormalized continuation credit for labelled inclusion numerators. -/
def numeratorCredit (items : List Item) (G : ℤ → ℝ≥0∞) : ℝ≥0∞ :=
  (items.map (fun a => (a.1 : ℝ≥0∞) * G a.2)).sum

private theorem numeratorCredit_append (xs ys : List Item) (G : ℤ → ℝ≥0∞) :
    numeratorCredit (xs ++ ys) G = numeratorCredit xs G + numeratorCredit ys G := by
  simp only [numeratorCredit, List.map_append, List.sum_append]

private theorem subtract_credit (amount : ℕ) (items : List Item)
    (h : ∀ a ∈ items, amount ≤ a.1) (G : ℤ → ℝ≥0∞) :
    numeratorCredit items G =
      (amount : ℝ≥0∞) * (items.map (fun a => G a.2)).sum +
        numeratorCredit (items.map (fun a => (a.1 - amount, a.2))) G := by
  induction items with
  | nil => simp [numeratorCredit]
  | cons a items ih =>
    have ha := h a (by simp)
    have ht : ∀ b ∈ items, amount ≤ b.1 := fun b hb => h b (by simp [hb])
    have hsplit : (a.1 : ℝ≥0∞) = amount + ((a.1 - amount : ℕ) : ℝ≥0∞) := by
      rw [← Nat.cast_add, Nat.add_sub_of_le ha]
    simp only [numeratorCredit, List.map_cons, List.sum_cons] at ih ⊢
    rw [hsplit, add_mul, ih ht, mul_add]
    ac_rfl

/-- One split preserves every labelled inclusion credit, including infinite credits. -/
theorem numeratorCredit_split (amount cutoff : ℕ) (items : List Item)
    (h : ∀ a ∈ items.drop cutoff, amount ≤ a.1) (G : ℤ → ℝ≥0∞) :
    numeratorCredit items G =
      (amount : ℝ≥0∞) * ((items.drop cutoff).map (fun a => G a.2)).sum +
        numeratorCredit (adjust amount cutoff items) G := by
  have hperm : List.Perm (adjust amount cutoff items) (trim amount cutoff items) :=
    List.perm_insertionSort ordered (trim amount cutoff items)
  have hsort := (hperm.map (fun a : Item => (a.1 : ℝ≥0∞) * G a.2)).sum_eq
  change numeratorCredit (adjust amount cutoff items) G =
    numeratorCredit (trim amount cutoff items) G at hsort
  have hparts := congrArg (fun xs => numeratorCredit xs G)
    (List.take_append_drop cutoff items)
  rw [numeratorCredit_append] at hparts
  rw [← hparts, subtract_credit amount (items.drop cutoff) h G, hsort, trim,
    numeratorCredit_append]
  ac_rfl

/-- The selected block and the rescaled residual form the normalized martingale. -/
theorem inclusion_credit_expectation (amount cutoff denominator : ℕ) (items : List Item)
    (h : ∀ a ∈ items.drop cutoff, amount ≤ a.1) (hd : amount < denominator)
    (G : ℤ → ℝ≥0∞) :
    (amount : ℝ≥0∞) / denominator * ((items.drop cutoff).map (fun a => G a.2)).sum +
      ((denominator - amount : ℕ) : ℝ≥0∞) / denominator *
        (numeratorCredit (adjust amount cutoff items) G / (denominator - amount : ℕ)) =
      numeratorCredit items G / denominator := by
  have hr : ((denominator - amount : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt hd).ne'
  have hcancel := ENNReal.mul_inv_cancel hr (by simp :
    ((denominator - amount : ℕ) : ℝ≥0∞) ≠ ⊤)
  rw [numeratorCredit_split amount cutoff items h G]
  simp only [ENNReal.div_eq_inv_mul]
  calc
    _ = (denominator : ℝ≥0∞)⁻¹ *
        ((amount : ℝ≥0∞) * ((items.drop cutoff).map (fun a => G a.2)).sum +
          (((denominator - amount : ℕ) : ℝ≥0∞) *
            ((denominator - amount : ℕ) : ℝ≥0∞)⁻¹) *
              numeratorCredit (adjust amount cutoff items) G) := by ring
    _ = _ := by rw [hcancel, one_mul]

end

end SampLib.SplittingPPS
