import SampLib.Distributions.FiniteGeometricWalk
import SampLib.Samplers.IterateCoin

/-! # Work estimates for Huber's adaptive power walk

Below the threshold the logistic walk drifts towards larger exponents. Above it,
the power selector survives with probability below `2/11`, paying for the work
increase when the probability margin is halved.
-/

open scoped BigOperators

namespace SampLib.AdaptivePowerWalk

noncomputable section

/-- The down/up logistic step preserves the requested power law. -/
theorem walk_bias (t : unitInterval) (n : ℕ) (hn : 0 < n) :
    CoinConditional.bias (IterateCoin.bias t (n - 1)) (IterateCoin.bias t (n + 1))
      (FiniteGeometricWalk.down t t.2.1) = IterateCoin.bias t n := by
  have hd : 0 < 1 + (t : ℝ) := by linarith [t.2.1]
  have hpow : (t : ℝ) ^ n = (t : ℝ) ^ (n - 1) * t := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  apply Subtype.ext
  simp only [CoinConditional.bias, Set.Icc.convexComb, IterateCoin.bias,
    FiniteGeometricWalk.down_coe]
  rw [pow_succ, hpow]
  field_simp [hd.ne']
  ring

def amplification (ε : ℝ) : ℝ := (2 - ε) / (2 * (1 - ε))

/-- A successful amplification retains half of the previous positive margin. -/
theorem amplification_margin (ε t : ℝ) (hε : ε < 1) (ht : t ≤ 1 - ε) :
    t * amplification ε ≤ 1 - ε / 2 := by
  have hden : 0 < 1 - ε := by linarith
  have hnum : 0 < 2 - ε := by linarith
  have hb : 0 ≤ amplification ε := by unfold amplification; positivity
  calc
    _ ≤ (1 - ε) * amplification ε := mul_le_mul_of_nonneg_right ht hb
    _ = _ := by unfold amplification; field_simp [hden.ne']

def selection (ε : ℝ) (n : ℕ) : ℝ := (2 * (1 - ε) / (2 - ε)) ^ n

/-- Accepting an amplified power exactly cancels the change of coefficient. -/
theorem amplification_preserves (ε t : ℝ) (hε : ε < 1) (n : ℕ) :
    selection ε n * (t * amplification ε) ^ n = t ^ n := by
  have hd : 0 < 1 - ε := by linarith
  have hd' : 0 < 2 - ε := by linarith
  rw [selection, ← mul_pow]
  congr 1
  unfold amplification
  field_simp [hd.ne', hd'.ne']

/-- The source's threshold makes surviving an amplification uniformly unlikely. -/
theorem selection_lt (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (n : ℕ)
    (hlarge : 355 / 100 < (n : ℝ) * ε) : selection ε n < 2 / 11 := by
  have hd : 0 < 2 - ε := by linarith
  have hb : 0 ≤ 2 * (1 - ε) / (2 - ε) := by positivity
  have hexp : 2 * (1 - ε) / (2 - ε) ≤ Real.exp (-ε / 2) := by
    calc
      _ ≤ 1 - ε / 2 := (div_le_iff₀ hd).mpr (by nlinarith [sq_nonneg ε])
      _ ≤ Real.exp (-ε / 2) := by linarith [Real.add_one_le_exp (-ε / 2)]
  have hbound : selection ε n ≤ Real.exp (-((n : ℝ) * ε / 2)) := by
    calc
      _ ≤ Real.exp (-ε / 2) ^ n := pow_le_pow_left₀ hb hexp n
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hconstant : (11 : ℝ) / 2 < Real.exp (355 / 200) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 355 / 200) 5
    norm_num [Finset.sum_range_succ] at h
    linarith
  calc
    _ ≤ Real.exp (-((n : ℝ) * ε / 2)) := hbound
    _ < Real.exp (-(355 / 200)) := Real.exp_lt_exp.mpr (by linarith)
    _ < 2 / 11 := by
      rw [Real.exp_neg]
      have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 11 / 2) hconstant
      norm_num at h ⊢
      exact h

/-- The reciprocal-margin work budget, clipped at the returning state. -/
private def work (ε : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else 30 / ε ^ 2 - (n : ℝ) / ε

@[simp] private theorem work_zero (ε : ℝ) : work ε 0 = 0 := by simp [work]

private theorem work_le_raw (ε : ℝ) (n : ℕ) :
    work ε n ≤ 30 / ε ^ 2 - (n : ℝ) / ε := by
  unfold work
  split_ifs with h
  · subst n
    simp only [Nat.cast_zero, zero_div, sub_zero]
    positivity
  · exact le_rfl

/-- A logistic step spends at least half a unit of work before amplification. -/
private theorem walk_drift (ε t : ℝ) (hε : 0 < ε) (ht : 0 ≤ t) (hmargin : t ≤ 1 - ε)
    (n : ℕ) (hn : 0 < n) :
    t / (1 + t) * work ε (n - 1) + 1 / (1 + t) * work ε (n + 1) + 1 / 2 ≤
      work ε n := by
  have hd : 0 < 1 + t := by positivity
  have hp : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn, Nat.cast_one]
  have hgap : 1 / 2 ≤ (1 - t) / (ε * (1 + t)) := by
    apply (le_div_iff₀ (mul_pos hε hd)).mpr
    have ht1 : t ≤ 1 := by linarith
    nlinarith
  have heq : t / (1 + t) * (30 / ε ^ 2 - ((n - 1 : ℕ) : ℝ) / ε) +
      1 / (1 + t) * (30 / ε ^ 2 - ((n + 1 : ℕ) : ℝ) / ε) =
      30 / ε ^ 2 - (n : ℝ) / ε - (1 - t) / (ε * (1 + t)) := by
    rw [hp, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  calc
    _ ≤ t / (1 + t) * (30 / ε ^ 2 - ((n - 1 : ℕ) : ℝ) / ε) +
        1 / (1 + t) * (30 / ε ^ 2 - ((n + 1 : ℕ) : ℝ) / ε) + 1 / 2 :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (work_le_raw ε (n - 1)) (div_nonneg ht hd.le))
        (mul_le_mul_of_nonneg_left (work_le_raw ε (n + 1))
          (show (0 : ℝ) ≤ 1 / (1 + t) by positivity))) le_rfl
    _ ≤ work ε n := by
      rw [heq, work, ite_eq_right (Nat.ne_of_gt hn)]
      linarith

/-- Capping the exponent term gives a positive budget for every initial exponent. -/
def budget (ε : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (60 - min (2 * (n : ℝ) * ε) (91 / 10)) / ε ^ 2

@[simp] theorem budget_zero (ε : ℝ) : budget ε 0 = 0 := by simp [budget]

theorem budget_nonneg (ε : ℝ) (n : ℕ) : 0 ≤ budget ε n := by
  unfold budget
  split_ifs
  · exact le_rfl
  · exact div_nonneg (by linarith [min_le_right (2 * (n : ℝ) * ε) (91 / 10)])
      (sq_nonneg ε)

private theorem budget_upper (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    budget ε n ≤ 60 / ε ^ 2 := by
  unfold budget
  split_ifs
  · positivity
  · apply div_le_div_of_nonneg_right _ (sq_nonneg ε)
    have hmin : 0 ≤ min (2 * (n : ℝ) * ε) (91 / 10) := by positivity
    linarith

private theorem budget_lower (ε : ℝ) (n : ℕ) (hn : 0 < n) :
    (509 / 10) / ε ^ 2 ≤ budget ε n := by
  rw [budget, ite_eq_right (Nat.ne_of_gt hn)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg ε)
  linarith [min_le_right (2 * (n : ℝ) * ε) (91 / 10)]

private theorem budget_eq (ε : ℝ) (n : ℕ)
    (hstate : (n : ℝ) * ε ≤ 455 / 100) : budget ε n = 2 * work ε n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [budget, work, ite_eq_right hn, ite_eq_right hn,
      min_eq_left (by linarith : 2 * (n : ℝ) * ε ≤ 91 / 10)]
    field_simp
    ring

/-- The capped budget also has strict drift through every ordinary walk step. -/
theorem walk_budget_drift (ε t : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (ht : 0 ≤ t) (hmargin : t ≤ 1 - ε) (n : ℕ) (hn : 0 < n)
    (hsmall : (n : ℝ) * ε ≤ 355 / 100) :
    t / (1 + t) * budget ε (n - 1) + 1 / (1 + t) * budget ε (n + 1) + 1 ≤
      budget ε n := by
  have hpred : ((n - 1 : ℕ) : ℝ) * ε ≤ 455 / 100 := by
    rw [Nat.cast_sub hn, Nat.cast_one]
    nlinarith
  have hsucc : ((n + 1 : ℕ) : ℝ) * ε ≤ 455 / 100 := by
    rw [Nat.cast_add, Nat.cast_one]
    nlinarith
  rw [budget_eq _ _ hpred, budget_eq _ _ hsucc, budget_eq _ _ (by linarith)]
  calc
    _ = 2 * (t / (1 + t) * work ε (n - 1) +
        1 / (1 + t) * work ε (n + 1) + 1 / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (walk_drift ε t hε ht hmargin n hn) (by norm_num)

/-- Rare survival funds both the halved-margin budget and amplified ambient credit. -/
theorem amplification_budget_drift (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (n : ℕ) (hn : 0 < n) (hlarge : 355 / 100 < (n : ℝ) * ε) :
    selection ε n * (budget (ε / 2) n + 2) ≤ budget ε n + 1 := by
  have hupper : budget (ε / 2) n ≤ 240 / ε ^ 2 := by
    convert budget_upper (ε / 2) (by positivity) n using 1
    field_simp
    norm_num
  calc
    _ ≤ (2 / 11) * (budget (ε / 2) n + 2) :=
      mul_le_mul_of_nonneg_right (selection_lt ε hε hε1 n hlarge).le
        (by linarith [budget_nonneg (ε / 2) n])
    _ ≤ (2 / 11) * (240 / ε ^ 2 + 2) := by gcongr
    _ = (480 / 11 + (4 / 11) * ε ^ 2) / ε ^ 2 := by
      field_simp
      ring
    _ ≤ (509 / 10 + ε ^ 2) / ε ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg ε)
      linarith [sq_nonneg ε]
    _ = (509 / 10) / ε ^ 2 + 1 := by field_simp
    _ ≤ budget ε n + 1 := add_le_add (budget_lower ε n hn) le_rfl

end

end SampLib.AdaptivePowerWalk
