import SampLib.Common.Laws.AbsorbingChain
import SampLib.Uniform.RationalCoin

/-! # The absorbing law of a power-series hazard factory

Each stage either returns true at the input coin, returns false at the hazard,
or continues. A vanishing survival product, rather than an expected-time bound,
normalizes the two marked exit masses.
-/

open MeasureTheory Measure
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.PowerSeriesHazards

noncomputable section

/-- Probability of reaching the following stage. -/
def continuation (p h : unitInterval) : ℝ≥0∞ := ofReal (1 - (p : ℝ)) * ofReal (1 - (h : ℝ))

/-- Expected credit paid by either exit at the current stage. -/
def exit (p h : unitInterval) (F : Bool → ℝ≥0∞) : ℝ≥0∞ :=
  ofReal (p : ℝ) * F true + ofReal (1 - (p : ℝ)) * ofReal (h : ℝ) * F false

theorem continuation_le_one (p h : unitInterval) : continuation p h ≤ 1 := by
  exact (mul_le_mul (ENNReal.ofReal_le_one.mpr (by linarith [p.2.1]))
    (ENNReal.ofReal_le_one.mpr (by linarith [h.2.1])) zero_le zero_le).trans_eq (one_mul 1)

private theorem exit_mass (p h : unitInterval) :
    ofReal (p : ℝ) + ofReal (1 - (p : ℝ)) * ofReal (h : ℝ) = 1 - continuation p h := by
  have hq : continuation p h = ofReal ((1 - (p : ℝ)) * (1 - (h : ℝ))) :=
    (ENNReal.ofReal_mul (sub_nonneg.mpr p.2.2)).symm
  rw [hq, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 (mul_nonneg (sub_nonneg.mpr p.2.2) (sub_nonneg.mpr h.2.2)),
    ← ENNReal.ofReal_mul (sub_nonneg.mpr p.2.2),
    ← ENNReal.ofReal_add p.2.1 (mul_nonneg (sub_nonneg.mpr p.2.2) h.2.1)]
  congr 1
  ring

/-- Both marked exits, summed over the number of preceding continuations. -/
def law (p : unitInterval) (h : ℕ → unitInterval) (start : ℕ) : Measure Bool :=
  Measure.sum (fun depth =>
    ((AbsorbingChain.survival (fun n => continuation p (h n)) start depth * ofReal (p : ℝ)) •
      dirac true) +
    ((AbsorbingChain.survival (fun n => continuation p (h n)) start depth *
      ofReal (1 - (p : ℝ)) * ofReal (h (start + depth) : ℝ)) • dirac false))

/-- The output law has total mass one exactly when no mass survives forever. -/
theorem isProbabilityMeasure_law (p : unitInterval) (h : ℕ → unitInterval) (start : ℕ)
    (absorbs : Filter.Tendsto
      (AbsorbingChain.survival (fun n => continuation p (h n)) start)
      Filter.atTop (nhds 0)) : IsProbabilityMeasure (law p h start) where
  measure_univ := by
    have hsum := AbsorbingChain.mass_sum (fun n => continuation p (h n))
      (fun n => continuation_le_one p (h n)) start absorbs
    simp only [law, Measure.sum_apply _ MeasurableSet.univ, Measure.add_apply,
      Measure.smul_apply, dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    convert hsum using 1
    apply tsum_congr
    intro depth
    rw [AbsorbingChain.mass, ← exit_mass]
    ring

/-- Integrate arbitrary continuation credit, including infinity, over the marked exits. -/
theorem lintegral_law (p : unitInterval) (h : ℕ → unitInterval)
    (start : ℕ) (F : Bool → ℝ≥0∞) :
    ∫⁻ b, F b ∂law p h start =
      ∑' depth, AbsorbingChain.survival (fun n => continuation p (h n)) start depth *
        exit p (h (start + depth)) F := by
  simp only [law, lintegral_sum_measure, lintegral_add_measure, lintegral_smul_measure,
    lintegral_dirac, smul_eq_mul]
  apply tsum_congr
  intro depth
  unfold exit
  ring

/-- First-stage exits and the surviving continuation preserve the full expectation. -/
theorem expectation (p : unitInterval) (h : ℕ → unitInterval)
    (start : ℕ) (F : Bool → ℝ≥0∞) :
    ∫⁻ b, F b ∂law p h start = exit p (h start) F +
      continuation p (h start) * ∫⁻ b, F b ∂law p h (start + 1) := by
  rw [lintegral_law, lintegral_law, tsum_eq_zero_add' ENNReal.summable,
    ← ENNReal.tsum_mul_left]
  simp only [AbsorbingChain.survival_zero, Nat.add_zero, one_mul]
  congr 1
  apply tsum_congr
  intro depth
  rw [AbsorbingChain.survival_succ, show start + (depth + 1) = start + 1 + depth by omega]
  ring

/-- Credit after the input coin; a failure still runs the hazard coin. -/
def kernel (h : unitInterval) (F : Bool → ℝ≥0∞) (c : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F true else RealCoin.credit h (fun b => if b then F false else c)

/-- Conditioning on the two coin calls separates both exits from the recursive branch. -/
theorem step_expectation (p h : unitInterval) (F : Bool → ℝ≥0∞) (c : ℝ≥0∞) :
    ∫⁻ b, kernel h F c b ∂RealCoin.law p = exit p h F + continuation p h * c := by
  simp only [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf, kernel,
    Bool.false_eq_true, ite_false, ite_true, exit, continuation]
  ring

/-- Removing the input-coin factors leaves the hazard-only survival product. -/
theorem survival_factor (p : unitInterval) (h : ℕ → unitInterval) (start depth : ℕ) :
    AbsorbingChain.survival (fun n => continuation p (h n)) start depth =
      ofReal (1 - (p : ℝ)) ^ depth *
        AbsorbingChain.survival (fun n => ofReal (1 - (h n : ℝ))) start depth := by
  induction depth generalizing start with
  | zero => simp
  | succ depth ih =>
    rw [AbsorbingChain.survival_succ, AbsorbingChain.survival_succ, ih, continuation, pow_succ]
    ring

/-- A normalized hazard-only scheme also terminates after adding input-coin exits. -/
theorem absorbs_of_hazards (p : unitInterval) (h : ℕ → unitInterval) (start : ℕ)
    (absorbs : Filter.Tendsto
      (AbsorbingChain.survival (fun n => ofReal (1 - (h n : ℝ))) start)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (AbsorbingChain.survival (fun n => continuation p (h n)) start)
      Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero] at absorbs ⊢
  intro ε hε
  filter_upwards [absorbs ε hε] with depth hd
  apply le_trans _ hd
  rw [survival_factor]
  exact mul_le_of_le_one_left zero_le
    (pow_le_one₀ zero_le (ENNReal.ofReal_le_one.mpr (by linarith [p.2.1])))

/-- Coefficient mass encoded by the successive source hazards. -/
def coefficient (h : ℕ → unitInterval) (n : ℕ) : ℝ≥0∞ :=
  AbsorbingChain.survival (fun n => ofReal (1 - (h n : ℝ))) 0 n * ofReal (h n : ℝ)

/-- The failure atom is the coefficient generating function evaluated at `1-p`. -/
theorem failure_probability (p : unitInterval) (h : ℕ → unitInterval) :
    law p h 0 {false} = ∑' n, coefficient h n * ofReal (1 - (p : ℝ)) ^ (n + 1) := by
  have ht : (dirac true : Measure Bool) {false} = 0 := by simp
  have hf : (dirac false : Measure Bool) {false} = 1 := by simp
  simp only [law, Measure.sum_apply _ (measurableSet_singleton false),
    Measure.add_apply, Measure.smul_apply, smul_eq_mul, ht, hf, mul_zero, zero_add, mul_one]
  apply tsum_congr
  intro n
  rw [survival_factor, coefficient, pow_succ]
  ring

private theorem coefficient_eq_mass (h : ℕ → unitInterval) (n : ℕ) :
    coefficient h n =
      AbsorbingChain.mass (fun n => ofReal (1 - (h n : ℝ))) 0 n := by
  have hsum := RealCoin.pmf_sum (h n)
  simp only [RealCoin.pmf, ite_true, Bool.false_eq_true, ite_false] at hsum
  have hc := ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top hsum
  simp only [coefficient, AbsorbingChain.mass, Nat.zero_add]
  rw [← hc]

/-- Coefficient mass one is the source's exact normalization assumption. -/
theorem absorbs_of_coefficient_sum (p : unitInterval) (h : ℕ → unitInterval)
    (normalized : ∑' n, coefficient h n = 1) :
    Filter.Tendsto (AbsorbingChain.survival (fun n => continuation p (h n)) 0)
      Filter.atTop (nhds 0) := by
  apply absorbs_of_hazards p h 0
  have hsurvival (depth : ℕ) :
      AbsorbingChain.survival (fun n => ofReal (1 - (h n : ℝ))) 0 depth =
        1 - ∑ i ∈ Finset.range depth, coefficient h i := by
    have he := AbsorbingChain.mass_partial_sum (fun n => ofReal (1 - (h n : ℝ)))
      (fun n => ENNReal.ofReal_le_one.mpr (by linarith [(h n).2.1])) 0 depth
    simp only [← coefficient_eq_mass] at he
    exact (ENNReal.sub_eq_of_eq_add_rev' (by simp) he.symm).symm
  have hfun : AbsorbingChain.survival (fun n => ofReal (1 - (h n : ℝ))) 0 =
      fun depth => 1 - ∑ i ∈ Finset.range depth, coefficient h i := funext hsurvival
  rw [hfun]
  have ht := (ENNReal.continuous_sub_left (a := 1) (by simp)).tendsto
    (∑' n, coefficient h n)
  have hh := ht.comp (ENNReal.tendsto_nat_tsum (coefficient h))
  simpa only [normalized, tsub_self, Function.comp_def] using hh

/-- The advertised complementary power-series law, under exact coefficient normalization. -/
theorem success_probability (p : unitInterval) (h : ℕ → unitInterval)
    (normalized : ∑' n, coefficient h n = 1) :
    law p h 0 {true} = 1 - ∑' n, coefficient h n * ofReal (1 - (p : ℝ)) ^ (n + 1) := by
  let := isProbabilityMeasure_law p h 0 (absorbs_of_coefficient_sum p h normalized)
  have hset : ({false} : Set Bool)ᶜ = {true} := by
    ext b
    cases b <;> simp
  rw [← hset, measure_compl (measurableSet_singleton false) (measure_ne_top _ _),
    measure_univ, failure_probability]

end

end SampLib.PowerSeriesHazards
