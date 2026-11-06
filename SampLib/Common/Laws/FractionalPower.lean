module

public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.PSeries
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # Mendo's reciprocal-hazard power factory

The probability of surviving the first `n` hazards is a generalized binomial
coefficient. Its generating function gives the output bias; the harmonic bound
also covers termination when the input coin never succeeds.
-/

open Filter Finset
open scoped BigOperators Topology

namespace SampLib.FractionalPower

noncomputable section

/-- Survival through the first `n` reciprocal hazards. -/
def survival (r : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => survival r n * (1 - r / (n + 1))

@[simp] theorem survival_zero (r : ℝ) : survival r 0 = 1 := rfl

@[simp] theorem survival_succ (r : ℝ) (n : ℕ) :
    survival r (n + 1) = survival r n * (1 - r / (n + 1)) := rfl

theorem hazard_mem {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    0 ≤ r / (n + 1) ∧ r / (n + 1) ≤ 1 := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  exact ⟨div_nonneg hr hn.le, (div_le_one hn).mpr (by linarith)⟩

theorem survival_mem {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    0 ≤ survival r n ∧ survival r n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h0, h1⟩ := hazard_mem hr hr1 n
    constructor
    · exact mul_nonneg ih.1 (sub_nonneg.mpr h1)
    · exact (mul_le_mul_of_nonneg_left (by linarith : 1 - r / (n + 1) ≤ 1) ih.1).trans
        (by simpa using ih.2)

/-- Reciprocal-hazard survival is bounded by the reciprocal accumulated hazard. -/
theorem survival_harmonic_bound {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    survival r n * (1 + r * ∑ j ∈ range n, (1 : ℝ) / (j + 1)) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs : 0 ≤ ∑ j ∈ range n, (1 : ℝ) / (j + 1) := sum_nonneg fun j _ => by positivity
    have hsur := (survival_mem hr hr1 n).1
    have hd : 0 ≤ r / (n + 1) := (hazard_mem hr hr1 n).1
    rw [survival_succ, sum_range_succ]
    have heq : 1 + r * ((∑ j ∈ range n, (1 : ℝ) / (j + 1)) + 1 / (n + 1)) =
        (1 + r * ∑ j ∈ range n, (1 : ℝ) / (j + 1)) + r / (n + 1) := by ring
    rw [heq]
    let A := 1 + r * ∑ j ∈ range n, (1 : ℝ) / (j + 1)
    let h := r / (n + 1)
    have hA : 1 ≤ A := le_add_of_nonneg_right (mul_nonneg hr hs)
    have hstep : (1 - h) * (A + h) ≤ A := by
      nlinarith [mul_nonneg hd (sub_nonneg.mpr hA), sq_nonneg h]
    change survival r n * (1 - h) * (A + h) ≤ 1
    calc
      _ = survival r n * ((1 - h) * (A + h)) := by ring
      _ ≤ survival r n * A := mul_le_mul_of_nonneg_left hstep hsur
      _ ≤ 1 := ih

/-- Even at zero input bias, a positive reciprocal hazard eventually stops. -/
theorem survival_tendsto_zero {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Tendsto (survival r) atTop (𝓝 0) := by
  have hsum : Tendsto (fun n : ℕ => ∑ j ∈ range n, (1 : ℝ) / (j + 1)) atTop atTop :=
    Real.tendsto_sum_range_one_div_nat_succ_atTop
  have hden : Tendsto (fun n : ℕ => 1 + r * ∑ j ∈ range n, (1 : ℝ) / (j + 1))
      atTop atTop :=
    tendsto_atTop_mono (fun n => le_add_of_nonneg_left zero_le_one) (hsum.const_mul_atTop hr)
  apply squeeze_zero (fun n => (survival_mem hr.le hr1 n).1)
      (fun n => ?_) hden.inv_tendsto_atTop
  have hpos : 0 < 1 + r * ∑ j ∈ range n, (1 : ℝ) / (j + 1) := by positivity
  simpa only [one_div, Pi.inv_apply] using
    (le_div_iff₀ hpos).mpr (survival_harmonic_bound hr.le hr1 n)

/-- Probability of reaching round `n+1`: both input and hazard must keep failing. -/
def roundSurvival (p r : ℝ) (n : ℕ) : ℝ := (1 - p) ^ n * survival r n

@[simp] theorem roundSurvival_zero (p r : ℝ) : roundSurvival p r 0 = 1 := by
  simp [roundSurvival]

theorem roundSurvival_succ (p r : ℝ) (n : ℕ) :
    roundSurvival p r (n + 1) =
      roundSurvival p r n * (1 - p) * (1 - r / (n + 1)) := by
  simp [roundSurvival, pow_succ, survival_succ]
  ring

theorem roundSurvival_nonneg {p r : ℝ} (_hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) : 0 ≤ roundSurvival p r n :=
  mul_nonneg (pow_nonneg (sub_nonneg.mpr hp1) _) (survival_mem hr hr1 n).1

/-- Positive input bias or positive exponent suffices for almost-sure stopping. -/
theorem roundSurvival_tendsto_zero {p r : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hstop : 0 < p ∨ 0 < r) :
    Tendsto (roundSurvival p r) atTop (𝓝 0) := by
  rcases hstop with hp0 | hr0
  · have hpow : Tendsto (fun n : ℕ => (1 - p) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
    apply squeeze_zero (roundSurvival_nonneg hp hp1 hr hr1) (fun n => ?_) hpow
    exact mul_le_of_le_one_right (pow_nonneg (sub_nonneg.mpr hp1) _)
      (survival_mem hr hr1 n).2
  · apply squeeze_zero (roundSurvival_nonneg hp hp1 hr hr1)
      (fun n => ?_) (survival_tendsto_zero hr0 hr1)
    exact mul_le_of_le_one_left (survival_mem hr hr1 n).1
      (pow_le_one₀ (by linarith) (by linarith))

/-- Mass of success in round `n+1`. -/
def successMass (p r : ℝ) (n : ℕ) : ℝ := roundSurvival p r n * p

/-- Mass of failure in round `n+1`. -/
def failureMass (p r : ℝ) (n : ℕ) : ℝ :=
  roundSurvival p r n * (1 - p) * (r / (n + 1))

/-- Each round partitions its incoming mass into its two exits and the next round. -/
theorem round_mass (p r : ℝ) (n : ℕ) :
    successMass p r n + failureMass p r n =
      roundSurvival p r n - roundSurvival p r (n + 1) := by
  rw [successMass, failureMass, roundSurvival_succ]
  ring

/-- The first-exit masses form a normalized law, including the heavy-tail endpoint. -/
theorem exit_hasSum {p r : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hstop : 0 < p ∨ 0 < r) :
    HasSum (fun n => successMass p r n + failureMass p r n) 1 := by
  have hnonneg : ∀ n, 0 ≤ successMass p r n + failureMass p r n := by
    intro n
    have hs := roundSurvival_nonneg hp hp1 hr hr1 n
    exact add_nonneg (mul_nonneg hs hp)
      (mul_nonneg (mul_nonneg hs (sub_nonneg.mpr hp1)) (hazard_mem hr hr1 n).1)
  apply (hasSum_iff_tendsto_nat_of_nonneg hnonneg 1).mpr
  have htel : ∀ N, ∑ n ∈ range N, (successMass p r n + failureMass p r n) =
      1 - roundSurvival p r N := by
    intro N
    simp_rw [round_mass]
    simpa using sum_range_sub' (roundSurvival p r) N
  simp_rw [htel]
  simpa using tendsto_const_nhds.sub (roundSurvival_tendsto_zero hp hp1 hr hr1 hstop)

private theorem multichoose_step (x : ℝ) (n : ℕ) :
    Ring.multichoose x (n + 1) = Ring.multichoose x n * (x + n) / (n + 1) := by
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer x (n + 1)
  rw [ascPochhammer_succ_right] at h
  simp only [Polynomial.smeval_mul, Polynomial.smeval_add, Polynomial.smeval_X,
    Polynomial.smeval_natCast, ← Ring.factorial_nsmul_multichoose_eq_ascPochhammer,
    nsmul_eq_mul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  apply (eq_div_iff hn1).mpr
  apply mul_left_cancel₀ hn
  nlinarith [h]

/-- The survival coefficients are precisely the binomial coefficients for exponent `1-r`. -/
theorem survival_eq_multichoose (r : ℝ) (n : ℕ) :
    survival r n = Ring.multichoose (1 - r) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [survival_succ, ih, multichoose_step]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

/-- The generalized binomial theorem identifies the success probability. -/
theorem success_hasSum {r p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    HasSum (fun n : ℕ => p * survival r n * (1 - p) ^ n) (p ^ r) := by
  have hx : 1 - p ∈ Metric.eball (0 : ℝ) 1 := by
    simpa [Metric.eball, edist_dist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hp1),
      ENNReal.ofReal_lt_one] using (by linarith : 1 - p < 1)
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1 - r)).hasSum hx
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add,
    sub_sub_cancel] at h
  have heq : p * (1 / p ^ (1 - r)) = p ^ r := by
    rw [one_div, ← Real.rpow_neg hp.le]
    calc
      p * p ^ (-(1 - r)) = p ^ (1 : ℝ) * p ^ (-(1 - r)) := by rw [Real.rpow_one]
      _ = p ^ (1 + -(1 - r)) := (Real.rpow_add hp _ _).symm
      _ = p ^ r := by congr 1; ring
  convert h.mul_left p using 1
  · ext n
    rw [survival_eq_multichoose, Ring.multichoose_eq]
    ring
  · exact heq.symm

/-- The success mass is `p^r`, including `p=0` whenever the exponent is positive. -/
theorem successMass_hasSum {p r : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hstop : 0 < p ∨ 0 < r) : HasSum (successMass p r) (p ^ r) := by
  rcases eq_or_lt_of_le hp with rfl | hp0
  · have hr : r ≠ 0 := by rcases hstop with h | h <;> linarith
    have hz : successMass 0 r = fun _ => 0 := by funext n; simp [successMass]
    rw [hz, Real.zero_rpow hr]
    exact hasSum_zero
  · convert success_hasSum (r := r) hp0 hp1 using 1
    ext n
    simp only [successMass, roundSurvival]
    ring

/-- The complementary exit mass follows from normalized first exits. -/
theorem failureMass_hasSum {p r : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hstop : 0 < p ∨ 0 < r) :
    HasSum (failureMass p r) (1 - p ^ r) := by
  simpa only [add_sub_cancel_left] using
    (exit_hasSum hp hp1 hr hr1 hstop).sub (successMass_hasSum hp hp1 hstop)

/-- Infinite continuation credits remain extended nonnegative reals throughout. -/
theorem successMass_tsum {p r : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hstop : 0 < p ∨ 0 < r) :
    ∑' n, ENNReal.ofReal (successMass p r n) = ENNReal.ofReal (p ^ r) := by
  have h := successMass_hasSum hp hp1 hstop
  rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg _ h.summable]
  intro n
  exact mul_nonneg (roundSurvival_nonneg hp hp1 hr hr1 n) hp

theorem failureMass_tsum {p r : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hstop : 0 < p ∨ 0 < r) :
    ∑' n, ENNReal.ofReal (failureMass p r n) = ENNReal.ofReal (1 - p ^ r) := by
  have h := failureMass_hasSum hp hp1 hr hr1 hstop
  rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg _ h.summable]
  intro n
  exact mul_nonneg (mul_nonneg (roundSurvival_nonneg hp hp1 hr hr1 n)
    (sub_nonneg.mpr hp1)) (hazard_mem hr hr1 n).1

end

end SampLib.FractionalPower
