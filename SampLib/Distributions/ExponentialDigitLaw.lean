import SampLib.Distributions.ExponentialDigitCells
import SampLib.Distributions.LatentReal.DigitKernel
import SampLib.Distributions.BernoulliMixture

/-! # The fractional exponential's conditional digit law

Every finite prefix is reachable. Its two children are the half-cells of its
dyadic interval, so the next bit has the source's location-independent logistic
bias. The posterior still retains the entire underlying fractional real.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SampLib.ExponentialDigits

noncomputable section

def lower (p : List Bool) : ℝ := (UniformBag.rank p : ℝ) / 2 ^ p.length
def upper (p : List Bool) : ℝ := ((UniformBag.rank p : ℝ) + 1) / 2 ^ p.length

private theorem cell_bounds (p : List Bool) :
    0 ≤ lower p ∧ lower p < upper p ∧ upper p ≤ 1 := by
  have hr := rank_bounds p
  have hD : (0 : ℝ) < 2 ^ p.length := by positivity
  refine ⟨div_nonneg (by exact_mod_cast hr.1) hD.le, ?_, ?_⟩
  · exact (div_lt_div_iff_of_pos_right hD).mpr (by linarith)
  · apply (div_le_one hD).mpr
    exact_mod_cast (show UniformBag.rank p + 1 ≤ (2 : ℤ) ^ p.length by omega)

private theorem rank_append (p : List Bool) (b : Bool) :
    UniformBag.rank (p ++ [b]) = 2 * UniformBag.rank p + if b then 1 else 0 := by
  induction p with
  | nil => simp [UniformBag.rank]
  | cons c p IH =>
    simp only [List.cons_append, UniformBag.rank, List.length_append, List.length_singleton,
      IH, pow_succ]
    ring

private theorem true_cell (p : List Bool) :
    Ico (lower (p ++ [true])) (upper (p ++ [true])) = Ico ((lower p + upper p) / 2) (upper p) := by
  have hD : (2 : ℝ) ^ p.length ≠ 0 := by positivity
  congr 1 <;> simp only [lower, upper, rank_append, ite_true, Int.cast_add, Int.cast_mul,
    Int.cast_ofNat, Int.cast_one, List.length_append, List.length_singleton, pow_succ] <;>
    field_simp <;> ring

/-- The canonical cylinder has exactly its dyadic interval's mass. -/
theorem cylinder_mass (rate : ℝ) (p : List Bool) :
    fraction rate (DigitPosterior.cylinder digits p) = fraction rate (Ico (lower p) (upper p)) :=
  measure_congr (cylinder_ae_cell rate p)

/-- Every prefix is reachable at every positive rate. -/
theorem cylinder_ne_zero (rate : ℝ) (hrate : 0 < rate) (p : List Bool) :
    fraction rate (DigitPosterior.cylinder digits p) ≠ 0 := by
  rw [cylinder_mass]
  exact fraction_interval_ne_zero rate hrate _ _ (cell_bounds p).1
    (cell_bounds p).2.1 (cell_bounds p).2.2

/-- The next canonical digit has the logistic bias at its dyadic width. -/
theorem next_success (rate : ℝ) (hrate : 0 < rate) (p : List Bool) :
    DigitPosterior.nextLaw (fraction rate) digits p {true} =
      ENNReal.ofReal (bitBias rate (1 / 2 ^ p.length) : ℝ) := by
  let := fraction_probability rate hrate
  rw [DigitPosterior.nextLaw_singleton _ measurable_digits, DigitPosterior.law,
    ProbabilityTheory.cond_apply (DigitPosterior.measurableSet_cylinder measurable_digits p),
    ← DigitPosterior.cylinder_extend, cylinder_mass, cylinder_mass, true_cell,
    fraction_half rate hrate _ _ (cell_bounds p).1 (cell_bounds p).2.1.le (cell_bounds p).2.2]
  have hw : upper p - lower p = 1 / 2 ^ p.length := by unfold lower upper; ring
  rw [hw]
  calc
    _ = ENNReal.ofReal (bitBias rate (1 / 2 ^ p.length) : ℝ) *
        ((fraction rate (Ico (lower p) (upper p)))⁻¹ *
          fraction rate (Ico (lower p) (upper p))) := by ring
    _ = _ := by
      rw [ENNReal.inv_mul_cancel
        (fraction_interval_ne_zero rate hrate _ _ (cell_bounds p).1
          (cell_bounds p).2.1 (cell_bounds p).2.2) (measure_ne_top _ _), mul_one]

/-- The full conditional bit law, ready for arbitrary joint posterior credits. -/
theorem next_law (rate : ℝ) (hrate : 0 < rate) (p : List Bool) :
    DigitPosterior.nextLaw (fraction rate) digits p =
      RealCoin.law (bitBias rate (1 / 2 ^ p.length)) := by
  let := fraction_probability rate hrate
  let := DigitPosterior.nextLaw_probability (fraction rate) measurable_digits p
    (cylinder_ne_zero rate hrate p)
  exact BernoulliMixture.eq_bernoulli_of_apply_true _ _ (next_success rate hrate p)

/-- The logistic bit bias is the success mass of the source's decay/retry trial. -/
theorem bitBias_coe_decay (rate width : ℝ) :
    (bitBias rate width : ℝ) = Real.exp (-(rate * width / 2)) /
      (1 + Real.exp (-(rate * width / 2))) := by
  dsimp [bitBias]
  rw [Real.exp_neg]
  field_simp
  ring

/-- Interpreting the canonical digit stream retains the fractional exponential law. -/
theorem value_law (rate : ℝ) :
    (fraction rate).map (fun x => DigitPosterior.value (digits x)) = fraction rate := by
  have hvalue : (fun x => DigitPosterior.value (digits x)) =ᵐ[fraction rate] id :=
    (fraction_support rate).mono fun x hx => value_digits hx
  rw [Measure.map_congr hvalue, Measure.map_id]

end

end SampLib.ExponentialDigits
