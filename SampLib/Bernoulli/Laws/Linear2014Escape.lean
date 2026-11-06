import SampLib.Bernoulli.Laws.Linear2014Jump

/-! # Uniform escape from a fixed stage of the expanding linear factory

A false input followed by at least `N` geometric failures exits every ordinary
state below the positive rational threshold `N/D`. This event gives one uniform
positive escape mass, independently of the current state.
-/

open MeasureTheory ProbabilityTheory
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.Linear2014Jump

noncomputable section

/-- The geometric upper tail, including the certain event at `L=0`. -/
theorem geometric_tail (q : unitInterval) (hq : 0 < (q : ℝ)) (L : ℕ) :
    (∫⁻ n, if L ≤ n then (1 : ℝ≥0∞) else 0 ∂geometricMeasure q) =
      ofReal ((1 - (q : ℝ)) ^ L) := by
  have hqne : q ≠ 0 := by intro h; simp [h] at hq
  induction L with
  | zero => simp
  | succ L IH =>
    rw [lintegral_geometricMeasure_succ q hqne]
    simp only [show ¬L + 1 ≤ 0 by omega, ite_false, mul_zero, zero_add,
      Nat.succ_le_succ_iff]
    rw [IH, ← ENNReal.ofReal_mul (sub_nonneg.mpr q.2.2), pow_succ']

/-- The complementary finite geometric interval has the expected finite mass. -/
theorem geometric_head (q : unitInterval) (hq : 0 < (q : ℝ)) (L : ℕ) :
    (∫⁻ n, if n < L then (1 : ℝ≥0∞) else 0 ∂geometricMeasure q) =
      ofReal (1 - (1 - (q : ℝ)) ^ L) := by
  have hnonneg : 0 ≤ (1 - (q : ℝ)) ^ L := pow_nonneg (sub_nonneg.mpr q.2.2) L
  have hle : (1 - (q : ℝ)) ^ L ≤ 1 :=
    pow_le_one₀ (sub_nonneg.mpr q.2.2) (by linarith [q.2.1])
  have hsum : (∫⁻ n, if n < L then (1 : ℝ≥0∞) else 0 ∂geometricMeasure q) +
      ofReal ((1 - (q : ℝ)) ^ L) = 1 := by
    rw [← geometric_tail q hq L, ← lintegral_add_left (measurable_of_countable _)]
    have hpartition (n : ℕ) :
        (if n < L then (1 : ℝ≥0∞) else 0) + (if L ≤ n then 1 else 0) = 1 := by
      by_cases h : n < L
      · simp only [h, not_le.mpr h, ite_true, ite_false, add_zero]
      · simp only [h, le_of_not_gt h, ite_false, ite_true, zero_add]
    simp_rw [hpartition]
    simp
  have htotal : ofReal (1 - (1 - (q : ℝ)) ^ L) + ofReal ((1 - (q : ℝ)) ^ L) = 1 := by
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr hle) hnonneg]
    simp
  exact (ENNReal.add_left_inj ENNReal.ofReal_ne_top).mp (hsum.trans htotal.symm)

/-- Indicator credit for an ordinary stage state. -/
def ordinary (N D n : ℕ) : ℝ≥0∞ := if 0 < n ∧ n * D < N then 1 else 0

private theorem ordinary_le_one (N D n : ℕ) : ordinary N D n ≤ 1 := by
  unfold ordinary
  split_ifs <;> simp

/-- A geometric jump of at least `N` escapes, since `D≥1`. -/
theorem geometric_ordinary_le (q : unitInterval) (hq : 0 < (q : ℝ))
    (N D s : ℕ) (hD : 0 < D) :
    (∫⁻ n, ordinary N D (s + n) ∂geometricMeasure q) ≤
      ofReal (1 - (1 - (q : ℝ)) ^ N) := by
  rw [← geometric_head q hq N]
  apply lintegral_mono
  intro n
  change (if 0 < s + n ∧ (s + n) * D < N then (1 : ℝ≥0∞) else 0) ≤
    (if n < N then 1 else 0)
  split_ifs with hstage hn
  · exact le_rfl
  · have hmul := Nat.le_mul_of_pos_right (s + n) hD
    omega
  · exact zero_le
  · exact le_rfl

/-- Uniform probability of the explicit false-trial/large-jump escape event. -/
def escape (p q : unitInterval) (N : ℕ) : ℝ := (1 - (p : ℝ)) * (1 - (q : ℝ)) ^ N

theorem escape_pos (p q : unitInterval) (hp : (p : ℝ) < 1) (hq : (q : ℝ) < 1)
    (N : ℕ) : 0 < escape p q N :=
  mul_pos (sub_pos.mpr hp) (pow_pos (sub_pos.mpr hq) _)

/-- The complete input-trial/jump mixture has a uniformly bounded ordinary mass. -/
theorem ordinary_expectation_le (p q : unitInterval) (hq : 0 < (q : ℝ))
    (N D s : ℕ) (hD : 0 < D) :
    (∫⁻ a, if a then ordinary N D (s - 1)
      else ∫⁻ n, ordinary N D (s + n) ∂geometricMeasure q ∂RealCoin.law p) ≤
        ofReal (1 - escape p q N) := by
  rw [RealCoin.lintegral_law]
  simp only [RealCoin.credit, RealCoin.pmf, ite_true, Bool.false_eq_true, ite_false]
  calc
    _ ≤ ofReal (p : ℝ) * 1 + ofReal (1 - (p : ℝ)) *
        ofReal (1 - (1 - (q : ℝ)) ^ N) := by
      gcongr
      · exact ordinary_le_one N D (s - 1)
      · exact geometric_ordinary_le q hq N D s hD
    _ = _ := by
      have htail : (1 - (q : ℝ)) ^ N ≤ 1 :=
        pow_le_one₀ (sub_nonneg.mpr q.2.2) (by linarith [q.2.1])
      rw [mul_one, ← ENNReal.ofReal_mul (sub_nonneg.mpr p.2.2),
        ← ENNReal.ofReal_add p.2.1
          (mul_nonneg (sub_nonneg.mpr p.2.2) (sub_nonneg.mpr htail))]
      congr 1
      unfold escape
      ring

/-- Bernoulli's inequality makes every boosted boundary return sufficiently unlikely. -/
theorem boosted_boundary (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) (hn : 2 ≤ n * ε) :
    1 / (1 + ε / 2) ^ n ≤ 1 / 2 := by
  have hbern := one_add_mul_le_pow (by linarith : -2 ≤ ε / 2) n
  have hden : 2 ≤ (1 + ε / 2) ^ n := by nlinarith
  exact (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)).mpr (by linarith)

end

end SampLib.Linear2014Jump
