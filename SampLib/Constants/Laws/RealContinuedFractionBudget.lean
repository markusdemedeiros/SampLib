module

public import SampLib.Constants.Laws.RealContinuedFraction

@[expose] public section

/-! # Credit potential for continued-fraction recursion

A position may call both its tail and itself. The potential `1 + 1/a` lies between one and
two, and both recursive calls together cost at most three quarters of it.
-/

open scoped NNReal

namespace SampLib.RealContinuedFraction

noncomputable section

/-- The branching recursion pays between one and two units at each position. -/
def potential (c : Coefficient) : ℝ≥0 :=
  ⟨1 + 1 / (c.denominator : ℝ),
    add_nonneg zero_le_one (div_nonneg zero_le_one c.denominator_pos.le)⟩

theorem one_le_potential (c : Coefficient) : 1 ≤ potential c := by
  change (1 : ℝ) ≤ 1 + 1 / (c.denominator : ℝ)
  exact le_add_of_nonneg_right (div_nonneg zero_le_one c.denominator_pos.le)

theorem potential_le_two (c : Coefficient) : potential c ≤ 2 := by
  have ha : (1 : ℝ) ≤ c.denominator := c.lower
  change 1 + 1 / (c.denominator : ℝ) ≤ 2
  have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) ha
  simp only [one_div_one] at this
  linarith

private theorem potential_le_value (a : ℕ → Coefficient) (i : ℕ)
    (hb : 1 ≤ (a i).numerator) :
    (potential (a i) : ℝ) ≤ 1 + 2 * (value a i : ℝ) := by
  have ha : (1 : ℝ) ≤ (a i).denominator := (a i).lower
  have hp := value_lower a i
  have hl : 1 / ((a i).denominator + 1 : ℝ) ≤ (value a i : ℝ) :=
    (div_le_div_of_nonneg_right hb (by positivity)).trans hp
  have ht : 1 / ((a i).denominator : ℝ) ≤
      2 / ((a i).denominator + 1 : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  change 1 + 1 / ((a i).denominator : ℝ) ≤ _
  simp only [div_eq_mul_inv, one_mul] at ht hl ⊢
  linarith

/-- Both recursive calls fit in three quarters of the current potential. -/
theorem recursive_budget (a : ℕ → Coefficient) (i : ℕ)
    (hprogress : 1 ≤ (a (i + 1)).numerator) :
    (1 / ((a i).denominator + 1 : ℝ)) *
        ((potential (a (i + 1)) : ℝ) +
          (1 - (value a (i + 1) : ℝ)) * (potential (a i) : ℝ)) ≤
      (3 / 4 : ℝ) * (potential (a i) : ℝ) := by
  have ha : (1 : ℝ) ≤ (a i).denominator := (a i).lower
  have ht := potential_le_value a (i + 1) hprogress
  have htwo : (potential (a i) : ℝ) ≤ 2 := potential_le_two (a i)
  have hp := (value a (i + 1)).2.2
  have hinside : (potential (a (i + 1)) : ℝ) +
      (1 - (value a (i + 1) : ℝ)) * (potential (a i) : ℝ) ≤ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr htwo)]
  calc
    _ ≤ (1 / ((a i).denominator + 1 : ℝ)) * 3 :=
      mul_le_mul_of_nonneg_left hinside (by positivity)
    _ ≤ _ := by
      change 1 / ((a i).denominator + 1 : ℝ) * 3 ≤
        3 / 4 * (1 + 1 / ((a i).denominator : ℝ))
      have ha0 : (0 : ℝ) < (a i).denominator := lt_of_lt_of_le zero_lt_one ha
      rw [show (3 / 4 : ℝ) * (1 + 1 / ((a i).denominator : ℝ)) =
        (3 * ((a i).denominator + 1)) / (4 * ((a i).denominator : ℝ)) by
          field_simp, one_div_mul_eq_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg ((a i).denominator - 1 : ℝ)]

end

end SampLib.RealContinuedFraction
