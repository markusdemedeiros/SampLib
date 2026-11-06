import SampLib.Bernoulli.Laws.ArctanSeries
import SampLib.Bernoulli.Laws.PiBoundsDefs

/-! # Exact source numerators for the analytic arctangent and Machin enclosures -/

open Filter
open scoped BigOperators Topology

namespace SampLib.PiBounds

noncomputable section

private theorem sign_real (n : ℕ) : (sign n : ℝ) = AlternatingEnclosure.sign n := by
  by_cases h : n % 2 = 0 <;> simp [sign, AlternatingEnclosure.sign, h]

theorem term_inverse (q n : ℕ) :
    (termDenominator q n : ℝ)⁻¹ = ArctanSeries.coefficient q n := by
  unfold termDenominator
  push_cast
  simp [ArctanSeries.coefficient, mul_inv_rev, inv_pow, div_eq_mul_inv, mul_comm]

def partialBefore (q n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, AlternatingEnclosure.sign k * ArctanSeries.coefficient q k

private theorem partialBefore_succ (q n : ℕ) :
    partialBefore q (n + 1) = partialBefore q n +
      AlternatingEnclosure.sign n * ArctanSeries.coefficient q n :=
  Finset.sum_range_succ _ _

/-- The integer accumulator represents precisely the terms preceding its current index. -/
theorem numerator_real (q n : ℕ) (hq : 2 ≤ q) :
    (numerator q n : ℝ) = partialBefore q n * (denominator q n : ℝ) := by
  induction n with
  | zero => simp [partialBefore]
  | succ n IH =>
    have ht : (termDenominator q n : ℝ) ≠ 0 :=
      by exact_mod_cast (termDenominator_pos q n hq).ne'
    rw [numerator_succ, denominator_succ, partialBefore_succ]
    push_cast
    rw [sign_real, IH, ← term_inverse]
    field_simp [ht]

/-- The raw lower fraction is the neighboring alternating partial-sum lower bound. -/
theorem arctan_lower_ratio (q n : ℕ) (hq : 2 ≤ q) :
    ((arctanRaw q n).1 : ℝ) / ((arctanRaw q n).2.2 : ℝ) = ArctanSeries.lower q n := by
  have hd : (denominator q n : ℝ) ≠ 0 := by exact_mod_cast (denominator_pos q n hq).ne'
  have ht : (termDenominator q n : ℝ) ≠ 0 :=
    by exact_mod_cast (termDenominator_pos q n hq).ne'
  have hpartial : AlternatingEnclosure.partialSum (ArctanSeries.coefficient q) n =
      partialBefore q (n + 1) := rfl
  by_cases hn : n % 2 = 0
  all_goals
    simp only [arctanRaw, ArctanSeries.lower, AlternatingEnclosure.lower, hpartial,
      partialBefore_succ, AlternatingEnclosure.sign, hn, ite_true, ite_false]
    rw [← term_inverse]
    push_cast
    rw [numerator_real q n hq]
    field_simp [hd, ht]
  all_goals ring

/-- The raw upper fraction is the other neighboring alternating partial sum. -/
theorem arctan_upper_ratio (q n : ℕ) (hq : 2 ≤ q) :
    ((arctanRaw q n).2.1 : ℝ) / ((arctanRaw q n).2.2 : ℝ) = ArctanSeries.upper q n := by
  have hd : (denominator q n : ℝ) ≠ 0 := by exact_mod_cast (denominator_pos q n hq).ne'
  have ht : (termDenominator q n : ℝ) ≠ 0 :=
    by exact_mod_cast (termDenominator_pos q n hq).ne'
  have hpartial : AlternatingEnclosure.partialSum (ArctanSeries.coefficient q) n =
      partialBefore q (n + 1) := rfl
  by_cases hn : n % 2 = 0
  all_goals
    simp only [arctanRaw, ArctanSeries.upper, AlternatingEnclosure.upper, hpartial,
      partialBefore_succ, AlternatingEnclosure.sign, hn, ite_true, ite_false]
    rw [← term_inverse]
    push_cast
    rw [numerator_real q n hq]
    field_simp [hd, ht]
  all_goals ring

theorem pi_lower_ratio (n : ℕ) :
    ((piRaw n).1 : ℝ) / ((piRaw n).2.2 : ℝ) = ArctanSeries.piLower n := by
  have ha : ((arctanRaw 5 (n + 1)).2.2 : ℝ) ≠ 0 :=
    by exact_mod_cast (arctanRaw_den_pos 5 (n + 1) (by decide)).ne'
  have hb : ((arctanRaw 239 (n + 1)).2.2 : ℝ) ≠ 0 :=
    by exact_mod_cast (arctanRaw_den_pos 239 (n + 1) (by decide)).ne'
  unfold piRaw ArctanSeries.piLower
  rw [← arctan_lower_ratio 5 (n + 1) (by decide),
    ← arctan_upper_ratio 239 (n + 1) (by decide)]
  push_cast
  field_simp [ha, hb]

theorem pi_upper_ratio (n : ℕ) :
    ((piRaw n).2.1 : ℝ) / ((piRaw n).2.2 : ℝ) = ArctanSeries.piUpper n := by
  have ha : ((arctanRaw 5 (n + 1)).2.2 : ℝ) ≠ 0 :=
    by exact_mod_cast (arctanRaw_den_pos 5 (n + 1) (by decide)).ne'
  have hb : ((arctanRaw 239 (n + 1)).2.2 : ℝ) ≠ 0 :=
    by exact_mod_cast (arctanRaw_den_pos 239 (n + 1) (by decide)).ne'
  unfold piRaw ArctanSeries.piUpper
  rw [← arctan_upper_ratio 5 (n + 1) (by decide),
    ← arctan_lower_ratio 239 (n + 1) (by decide)]
  push_cast
  field_simp [ha, hb]

private theorem denominator_real (n : ℕ) :
    (((piRaw n).2.2).toNat : ℝ) = ((piRaw n).2.2 : ℝ) := by
  exact_mod_cast Int.toNat_of_nonneg (piRaw_den_pos n).le

/-- The concrete integer gateway encloses the actual mathematical constant π. -/
def interval (n : ℕ) : RealEnclosure.Interval Real.pi where
  lower := (piRaw n).1
  upper := (piRaw n).2.1
  denominator := (piRaw n).2.2.toNat
  positive := by have := piRaw_den_pos n; omega
  below := by
    rw [denominator_real]
    apply (div_le_iff₀ (by exact_mod_cast piRaw_den_pos n)).mp
    rw [pi_lower_ratio]
    exact (ArctanSeries.pi_mem n).1
  above := by
    rw [denominator_real]
    apply (le_div_iff₀ (by exact_mod_cast piRaw_den_pos n)).mp
    rw [pi_upper_ratio]
    exact (ArctanSeries.pi_mem n).2

@[simp] theorem interval_left (n : ℕ) : (interval n).left = ArctanSeries.piLower n := by
  simpa only [RealEnclosure.Interval.left, interval, denominator_real] using pi_lower_ratio n

@[simp] theorem interval_right (n : ℕ) : (interval n).right = ArctanSeries.piUpper n := by
  simpa only [RealEnclosure.Interval.right, interval, denominator_real] using pi_upper_ratio n

theorem interval_positive (n : ℕ) : 3 < (interval n).left := by
  rw [interval_left]
  exact ArctanSeries.pi_lower_gt_three n

theorem interval_width_tendsto :
    Tendsto (fun n => (interval n).width) atTop (𝓝 0) := by
  simpa only [RealEnclosure.Interval.width, interval_left, interval_right] using
    ArctanSeries.pi_width_tendsto

theorem interval_tight : RealEnclosure.Tight interval :=
  RealEnclosure.Tight.of_tendsto interval interval_width_tendsto

@[simp] theorem interval_triple (n : ℕ) : (interval n).triple = piRaw n := by
  unfold RealEnclosure.Interval.triple interval
  rw [Int.toNat_of_nonneg (piRaw_den_pos n).le]

@[simp] theorem encode_interval {rT : Type} (n : ℕ) :
    RealEnclosure.encodeInterval (rT := rT) (interval n) = encodeTriple (piRaw n) := by
  rw [RealEnclosure.encodeInterval, interval_triple]

end

end SampLib.PiBounds
