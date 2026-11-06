module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! # Positive real continued fractions bounded away from zero

Finite prefixes act on the possible tail interval `[0,1]`. Their images form
nested compact intervals. Every two coefficients contract distances by at least
a factor of four, so their intersection identifies the infinite fraction.
-/

open Set
open scoped NNReal

namespace SampLib.RealContinuedFraction

noncomputable section

/-- Positive reciprocal coefficients with denominator at least one. -/
structure Coefficient where
  numerator : ℝ
  denominator : ℝ
  positive : 0 < numerator
  lower : 1 ≤ denominator
  bounded : numerator ≤ denominator
  last : Bool

theorem Coefficient.denominator_pos (c : Coefficient) : 0 < c.denominator :=
  lt_of_lt_of_le zero_lt_one c.lower

def tailInput (c : Coefficient) (x : unitInterval) : unitInterval :=
  if c.last then 0 else x

/-- One coefficient acts by `b/(a+x)`; a final coefficient ignores the tail. -/
def step (c : Coefficient) (x : unitInterval) : unitInterval :=
  ⟨(c.numerator : ℝ) / (c.denominator + (tailInput c x : ℝ)),
    div_nonneg c.positive.le
      (add_nonneg c.denominator_pos.le (tailInput c x).2.1), by
      have ha : (0 : ℝ) < c.denominator := by exact_mod_cast c.denominator_pos
      have hb : (c.numerator : ℝ) ≤ c.denominator := by exact_mod_cast c.bounded
      apply (div_le_one (add_pos_of_pos_of_nonneg ha (tailInput c x).2.1)).mpr
      exact hb.trans (le_add_of_nonneg_right (tailInput c x).2.1)⟩

/-- Apply the first `n` coefficients to an arbitrary terminal tail. -/
def expand (a : ℕ → Coefficient) (i : ℕ) : ℕ → unitInterval → unitInterval
  | 0, x => x
  | n + 1, x => step (a i) (expand a (i + 1) n x)

theorem continuous_step (c : Coefficient) : Continuous (step c) := by
  unfold step
  apply Continuous.subtype_mk
  have ha : (0 : ℝ) < c.denominator := by exact_mod_cast c.denominator_pos
  have ht : Continuous (fun x : unitInterval => (tailInput c x : ℝ)) := by
    cases h : c.last <;> simp [tailInput, h] <;> fun_prop
  exact continuous_const.div (continuous_const.add ht)
    (fun x => (add_pos_of_pos_of_nonneg ha (tailInput c x).2.1).ne')

theorem continuous_expand (a : ℕ → Coefficient) (i n : ℕ) : Continuous (expand a i n) := by
  induction n generalizing i with
  | zero => exact continuous_id
  | succ n IH => exact (continuous_step (a i)).comp (IH (i + 1))

theorem expand_add (a : ℕ → Coefficient) (i n m : ℕ) (x : unitInterval) :
    expand a i (n + m) x = expand a i n (expand a (i + n) m x) := by
  induction n generalizing i with
  | zero => simp [expand]
  | succ n IH =>
    simpa [expand, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      congrArg (step (a i)) (IH (i + 1))

private theorem nested (a : ℕ → Coefficient) (i n : ℕ) :
    range (expand a i (n + 1)) ⊆ range (expand a i n) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨step (a (i + n)) x, by simpa [expand] using (expand_add a i n 1 x).symm⟩

/-- A continued fraction has at least one value compatible with every finite prefix. -/
theorem exists_value (a : ℕ → Coefficient) (i : ℕ) :
    (⋂ n : ℕ, range (expand a i n)).Nonempty := by
  apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
  · exact nested a i
  · exact fun n => ⟨expand a i n 0, 0, rfl⟩
  · simpa [expand] using (isCompact_univ : IsCompact (univ : Set unitInterval))
  · exact fun n => (isCompact_range (continuous_expand a i n)).isClosed

/-- The real value enclosed by all finite continued-fraction prefixes. -/
def value (a : ℕ → Coefficient) (i : ℕ) : unitInterval :=
  Classical.choose (exists_value a i)

theorem value_mem (a : ℕ → Coefficient) (i n : ℕ) :
    value a i ∈ range (expand a i n) :=
  mem_iInter.mp (Classical.choose_spec (exists_value a i)) n

private theorem pair_difference (a b c d x y : ℝ)
    (hx : a * (c + x) + d ≠ 0) (hy : a * (c + y) + d ≠ 0) :
    b * (c + x) / (a * (c + x) + d) - b * (c + y) / (a * (c + y) + d) =
      (b * d / ((a * (c + x) + d) * (a * (c + y) + d))) * (x - y) := by
  rw [div_sub_div _ _ hx hy, div_mul_eq_mul_div]
  congr 1
  ring

/-- Two positive reciprocal maps contract uniformly, even for unbounded coefficients. -/
private theorem ratio_pair_lipschitz (a b c d : ℝ) (ha : 1 ≤ a) (hb : 0 ≤ b)
    (hba : b ≤ a) (hc : 1 ≤ c) (hd : 0 ≤ d) :
    LipschitzWith (1 / 4) (fun x : unitInterval => b * (c + x) / (a * (c + x) + d)) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hden (x : unitInterval) : 0 < a * (c + (x : ℝ)) + d :=
    add_pos_of_pos_of_nonneg (mul_pos ha0 (add_pos_of_pos_of_nonneg hc0 x.2.1)) hd
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  change |b * (c + (x : ℝ)) / (a * (c + x) + d) -
      b * (c + (y : ℝ)) / (a * (c + y) + d)| ≤ (1 / 4 : ℝ) * |(x : ℝ) - y|
  have hbd : b * d ≤ a * c * d :=
    (mul_le_mul_of_nonneg_right hba hd).trans
      (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right ha0.le hc) hd)
  have hC : 0 ≤ a * c + d := add_nonneg (mul_nonneg ha0.le hc0.le) hd
  have hx : a * c + d ≤ a * (c + (x : ℝ)) + d := by
    nlinarith [mul_nonneg ha0.le x.2.1]
  have hy : a * c + d ≤ a * (c + (y : ℝ)) + d := by
    nlinarith [mul_nonneg ha0.le y.2.1]
  have hmul := mul_le_mul hx hy hC (hden x).le
  have hprod : 4 * (b * d) ≤ (a * (c + (x : ℝ)) + d) * (a * (c + (y : ℝ)) + d) := by
    nlinarith [sq_nonneg (a * c - d)]
  have hratio : b * d / ((a * (c + (x : ℝ)) + d) * (a * (c + (y : ℝ)) + d)) ≤ 1 / 4 := by
    apply (div_le_iff₀ (mul_pos (hden x) (hden y))).mpr
    nlinarith
  rw [pair_difference a b c d x y (hden x).ne' (hden y).ne', abs_mul,
    abs_of_nonneg (div_nonneg (mul_nonneg hb hd) (mul_pos (hden x) (hden y)).le)]
  exact mul_le_mul_of_nonneg_right hratio (abs_nonneg _)

private theorem step_pair_coe (c d : Coefficient) (hc : c.last ≠ true) (hd : d.last ≠ true)
    (x : unitInterval) :
    (step c (step d x) : ℝ) =
      (c.numerator : ℝ) * (d.denominator + (x : ℝ)) /
        (c.denominator * (d.denominator + (x : ℝ)) + d.numerator) := by
  have ha : (0 : ℝ) < c.denominator := by exact_mod_cast c.denominator_pos
  have hb : (0 : ℝ) < d.denominator := by exact_mod_cast d.denominator_pos
  have hnum : (0 : ℝ) ≤ d.numerator := d.positive.le
  have hden : 0 < (d.denominator : ℝ) + (x : ℝ) := add_pos_of_pos_of_nonneg hb x.2.1
  have hprod : 0 < (c.denominator : ℝ) * (d.denominator + (x : ℝ)) + d.numerator :=
    add_pos_of_pos_of_nonneg (mul_pos ha hden) hnum
  dsimp only [step]
  simp [tailInput, hc, hd]
  field_simp

theorem pair_lipschitz (c d : Coefficient) :
    LipschitzWith (1 / 4) (fun x => step c (step d x)) := by
  by_cases hc : c.last = true
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp [step, tailInput, hc]
  · by_cases hd : d.last = true
    · refine LipschitzWith.of_dist_le_mul fun x y => ?_
      simp [step, tailInput, hd]
    · have ha : (1 : ℝ) ≤ c.denominator := c.lower
      have ha' : (1 : ℝ) ≤ d.denominator := d.lower
      have hba : (c.numerator : ℝ) ≤ c.denominator := by exact_mod_cast c.bounded
      have h := ratio_pair_lipschitz c.denominator c.numerator d.denominator d.numerator
        ha c.positive.le hba ha' d.positive.le
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      change |(step c (step d x) : ℝ) - (step c (step d y) : ℝ)| ≤
        (1 / 4 : ℝ) * |(x : ℝ) - y|
      rw [step_pair_coe c d hc hd, step_pair_coe c d hc hd]
      exact h.dist_le_mul x y

/-- Every pair of coefficients removes a factor of four of tail uncertainty. -/
theorem expand_even_lipschitz (a : ℕ → Coefficient) (i n : ℕ) :
    LipschitzWith ((1 / 4) ^ n) (expand a i (2 * n)) := by
  induction n generalizing i with
  | zero =>
    change LipschitzWith 1 (id : unitInterval → _)
    exact LipschitzWith.id
  | succ n IH =>
    have h := (pair_lipschitz (a i) (a (i + 1))).comp (IH (i + 2))
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    change LipschitzWith ((1 / 4) ^ (n + 1))
      (fun x => step (a i) (step (a (i + 1)) (expand a (i + 1 + 1) (2 * n) x)))
    simpa only [pow_succ, mul_comm, Function.comp_def, Nat.add_assoc] using h

/-- No two values can remain in every finite-prefix interval. -/
theorem unique_value (a : ℕ → Coefficient) (i : ℕ) (x y : unitInterval)
    (hx : ∀ n, x ∈ range (expand a i n)) (hy : ∀ n, y ∈ range (expand a i n)) :
    x = y := by
  have hbound (n : ℕ) : dist x y ≤ (1 / 4 : ℝ) ^ n := by
    obtain ⟨u, rfl⟩ := hx (2 * n)
    obtain ⟨v, rfl⟩ := hy (2 * n)
    have huv : dist u v ≤ 1 := by
      change |(u : ℝ) - v| ≤ 1
      exact abs_le.mpr ⟨by linarith [u.2.1, v.2.2], by linarith [u.2.2, v.2.1]⟩
    simpa using (expand_even_lipschitz a i n).dist_le_mul_of_le huv
  have hz := le_of_tendsto_of_tendsto' tendsto_const_nhds
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)) hbound
  exact dist_eq_zero.mp (le_antisymm hz dist_nonneg)

/-- The canonical fraction satisfies its usual tail recurrence. -/
theorem value_step (a : ℕ → Coefficient) (i : ℕ) :
    value a i = step (a i) (value a (i + 1)) := by
  apply unique_value a i
  · exact value_mem a i
  · intro n
    cases n with
    | zero => exact ⟨_, rfl⟩
    | succ n =>
      obtain ⟨x, hx⟩ := value_mem a (i + 1) n
      exact ⟨x, by simpa [expand] using congrArg (step (a i)) hx⟩

/-- A final flag makes the fraction independent of every later coefficient. -/
theorem value_coe (a : ℕ → Coefficient) (i : ℕ) :
    (value a i : ℝ) = (a i).numerator /
      ((a i).denominator + if (a i).last then 0 else (value a (i + 1) : ℝ)) := by
  rw [value_step]
  cases h : (a i).last <;> simp [step, tailInput, h]

theorem value_pos (a : ℕ → Coefficient) (i : ℕ) : 0 < (value a i : ℝ) := by
  rw [value_step]
  change 0 < (a i).numerator / ((a i).denominator + (tailInput (a i) _ : ℝ))
  have hb : (0 : ℝ) < (a i).numerator := (a i).positive
  have ha : (0 : ℝ) < (a i).denominator := by exact_mod_cast (a i).denominator_pos
  exact div_pos hb (add_pos_of_pos_of_nonneg ha (tailInput (a i) _).2.1)

theorem value_lower (a : ℕ → Coefficient) (i : ℕ) :
    (a i).numerator / ((a i).denominator + 1 : ℝ) ≤ (value a i : ℝ) := by
  rw [value_step]
  change (a i).numerator / ((a i).denominator + 1 : ℝ) ≤
    (a i).numerator / ((a i).denominator + (tailInput (a i) _ : ℝ))
  have ha : (0 : ℝ) < (a i).denominator := by exact_mod_cast (a i).denominator_pos
  exact div_le_div_of_nonneg_left (a i).positive.le
    (add_pos_of_pos_of_nonneg ha (tailInput (a i) _).2.1)
    (by linarith [(tailInput (a i) (value a (i + 1))).2.2])

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
