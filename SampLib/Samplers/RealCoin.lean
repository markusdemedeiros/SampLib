import SampLib.Templates
import Samplers.Uniform
import Metrology.Iris.LocalBI

/-!
# Continuous threshold Bernoulli sampler

CTE verification of `Occil.realCoin` over mathematical reals:

1. Specify the target law and expected continuation credit.
2. Construct a measurable credit kernel for the uniform draw.
3. Prove credit conservation and the total-WP specification.

`realCoin_distSpec` packages the result as `IsDistSpec` for every `p ∈ [0, 1]`.
-/

open Set ProbLang
open ENNReal (ofReal ofReal_add)
open ProbLangℝ (realLt realOfInt)
open LawfulProbLangℝ (unifUnit)
open scoped ENNReal

namespace SampLib.RealCoin

noncomputable section

section distribution

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

end distribution

section creditExpectation

/-- Expected continuation credit. -/
def credit (p : unitInterval) (F : Bool → ℝ≥0∞) : ℝ≥0∞ :=
  pmf p true * F true + pmf p false * F false

/-- Expectation under `law`. -/
theorem lintegral_law (p : unitInterval) (F : Bool → ℝ≥0∞) :
    ∫⁻ b, F b ∂law p = credit p F := by
  simp [law, credit, smul_eq_mul]

end creditExpectation

section creditKernel

/-- Credit assigned to a uniform draw. -/
def uniformCredit (p : unitInterval) (F : Bool → ℝ≥0∞) (r : ℝ) : ℝ≥0∞ :=
  if r < p then F true else F false

/-- Credit of the resulting Boolean. -/
theorem uniformCredit_eq (p : unitInterval) (F : Bool → ℝ≥0∞) (r : ℝ) :
    uniformCredit p F r = F (decide (r < (p : ℝ))) := by
  by_cases hr : r < p <;> simp [uniformCredit, hr]

end creditKernel

section measurability

theorem measurable_uniformCredit (p : unitInterval) (F : Bool → ℝ≥0∞) :
    Measurable (uniformCredit p F) :=
  Measurable.ite measurableSet_Iio measurable_const measurable_const

end measurability

section conservation

open MeasureTheory

/-- The uniform credit kernel conserves the Bernoulli expectation. -/
theorem lintegral_uniformCredit (p : unitInterval) (F : Bool → ℝ≥0∞) :
    ∫⁻ r, uniformCredit p F r ∂unifUnit = credit p F := by
  change ∫⁻ r in Icc (0 : ℝ) 1,
    (Iio (p : ℝ)).piecewise (fun _ => F true) (fun _ => F false) r = _
  rw [← restrict_Ico_eq_restrict_Icc,
    lintegral_piecewise measurableSet_Iio.nullMeasurableSet]
  simp [Measure.restrict_apply' measurableSet_Ico, inter_comm _ (Ico (0 : ℝ) 1),
    credit, pmf, min_eq_right p.2.2, max_eq_right p.2.1, mul_comm]

end conservation

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

/-- Unit-interval inputs pass the domain check. -/
private theorem realCoin_guard (p : unitInterval) :
    (realLt (p : ℝ) (realOfInt 0) || realLt (realOfInt 1) (p : ℝ)) = false := by
  simp [realLt, realOfInt, not_lt.mpr p.2.1, not_lt.mpr p.2.2]

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

/-- CTE specification with arbitrary continuation credits. -/
theorem twp_realCoin (E : CoPset) (p : unitInterval) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (credit p F) -∗
      tglWp E pl(&Occil.realCoin #real (p : ℝ))
        (fun v : Val ℝ => iprop(∃ b : Bool, ⌜v.1 = .lit (.bool b)⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  twp_pures
  rw [realCoin_guard p]
  twp_pures
  -- Redistribute the initial credit across the uniform draw.
  twp_bind pl(urand)
  iapply (twp_urand_exp (measurable_uniformCredit p F) ?_) $$ Hcredit
  · rw [lintegral_uniformCredit]
  iintro %r ⟨_, Hcredit⟩
  twp_pures
  twp_value
  imodintro
  iexists (decide (r < (p : ℝ)))
  -- The sampled credit is exactly the continuation credit of this result.
  isimp only [uniformCredit_eq] at Hcredit
  iframe Hcredit
  ipureintro
  rfl

/-- Typed distribution specification. -/
theorem realCoin_distSpec (E : CoPset) (p : unitInterval) :
    IsDistSpec (GF := GF) E pl(&Occil.realCoin #real (p : ℝ)) (law p) Val.bool where
  spec F _ := by
    simpa only [lintegral_law, Val.ext_iff] using wand_entails (twp_realCoin E p F)

end specification

end

end SampLib.RealCoin
