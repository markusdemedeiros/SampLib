module

public import Metrology.ProbLang.Reals
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Topology.UnitInterval

@[expose] public section

/-!
# Bernoulli law and its uniform threshold kernel

`law p` is the Bernoulli measure with bias `p`. A uniform draw `r` on the unit interval
carries the credit of `decide (r < p)`, and this kernel conserves the Bernoulli expectation.
-/

open Set ProbLang
open ENNReal (ofReal ofReal_add)
open LawfulProbLangℝ (unifUnit)
open scoped ENNReal

namespace SampLib.RealCoin

noncomputable section

open MeasureTheory Measure

/-- Bernoulli mass function. -/
def pmf (p : unitInterval) (b : Bool) : ℝ≥0∞ :=
  if b then ofReal p else ofReal (1 - (p : ℝ))

theorem pmf_sum (p : unitInterval) : pmf p true + pmf p false = 1 := by
  simp [pmf, ← ofReal_add p.2.1 (sub_nonneg.mpr p.2.2)]

/-- Bernoulli probability measure. -/
def law (p : unitInterval) : Measure Bool :=
  (pmf p true • dirac true) + (pmf p false • dirac false)

instance (p : unitInterval) : IsProbabilityMeasure (law p) where
  measure_univ := by simpa [law] using pmf_sum p

/-- Expected continuation credit. -/
def credit (p : unitInterval) (F : Bool → ℝ≥0∞) : ℝ≥0∞ :=
  pmf p true * F true + pmf p false * F false

/-- Expectation under `law`. -/
theorem lintegral_law (p : unitInterval) (F : Bool → ℝ≥0∞) :
    ∫⁻ b, F b ∂law p = credit p F := by
  simp [law, credit, smul_eq_mul]

/-- Credit assigned to a uniform draw. -/
def uniformCredit (p : unitInterval) (F : Bool → ℝ≥0∞) (r : ℝ) : ℝ≥0∞ :=
  if r < p then F true else F false

/-- Credit of the resulting Boolean. -/
theorem uniformCredit_eq (p : unitInterval) (F : Bool → ℝ≥0∞) (r : ℝ) :
    uniformCredit p F r = F (decide (r < (p : ℝ))) := by
  by_cases hr : r < p <;> simp [uniformCredit, hr]

theorem measurable_uniformCredit (p : unitInterval) (F : Bool → ℝ≥0∞) :
    Measurable (uniformCredit p F) :=
  Measurable.ite measurableSet_Iio measurable_const measurable_const

/-- The uniform credit kernel conserves the Bernoulli expectation. -/
theorem lintegral_uniformCredit (p : unitInterval) (F : Bool → ℝ≥0∞) :
    ∫⁻ r, uniformCredit p F r ∂unifUnit = credit p F := by
  change ∫⁻ r in Icc (0 : ℝ) 1,
    (Iio (p : ℝ)).piecewise (fun _ => F true) (fun _ => F false) r = _
  rw [← restrict_Ico_eq_restrict_Icc,
    lintegral_piecewise measurableSet_Iio.nullMeasurableSet]
  simp [Measure.restrict_apply' measurableSet_Ico, inter_comm _ (Ico (0 : ℝ) 1),
    credit, pmf, min_eq_right p.2.2, max_eq_right p.2.1, mul_comm]

end

end SampLib.RealCoin
