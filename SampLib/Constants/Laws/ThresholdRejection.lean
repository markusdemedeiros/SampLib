import SampLib.Common.Laws.AcceptedProposal
import SampLib.Common.Laws.BooleanEvent

/-! # Threshold observations after value-dependent rejection

Normalize the accepted proposal first, then observe its threshold event. This
separates the density argument from program execution and preserves infinite credits.
-/

open Set MeasureTheory
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.ThresholdRejection

noncomputable section

def event (x t : ℝ) : Bool := if t < x then true else false

theorem event_eq_decide (x t : ℝ) : event x t = decide (t < x) := by
  by_cases h : t < x <;> simp [event, h]

theorem measurable_event (x : ℝ) : Measurable (event x) := by
  unfold event
  exact Measurable.ite measurableSet_Iio measurable_const measurable_const

theorem event_preimage (x : ℝ) : event x ⁻¹' {true} = Iio x := by
  ext t
  by_cases h : t < x <;> simp [event, h]

variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : ℝ → unitInterval)

theorem mass_ne_zero (hg : Measurable g) (hpos : ∀ t, 0 < (g t : ℝ)) :
    AcceptedProposal.mass μ g ≠ 0 := by
  apply ne_of_gt
  apply (lintegral_pos_iff_support (AcceptedProposal.measurable_weight g hg)).mpr
  have hs : Function.support (AcceptedProposal.weight g) = univ := by
    ext t
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (ENNReal.ofReal_pos.mpr (hpos t)).ne'
  rw [hs, measure_univ]
  exact zero_lt_one

def bias (hmass : AcceptedProposal.mass μ g ≠ 0) (x : ℝ) : unitInterval :=
  BooleanEvent.bias (AcceptedProposal.law μ g hmass) (event x)

theorem credit_eq (hmass : AcceptedProposal.mass μ g ≠ 0) (x : ℝ)
    (F : Bool → ℝ≥0∞) :
    ∫⁻ t, F (event x t) ∂AcceptedProposal.law μ g hmass =
      RealCoin.credit (bias μ g hmass x) F := by
  simpa only [bias, RealCoin.lintegral_law] using
    BooleanEvent.expectation (AcceptedProposal.law μ g hmass) (event x) (measurable_event x) F

/-- Its success probability is the normalized accepted mass below the threshold. -/
theorem bias_coe (hmass : AcceptedProposal.mass μ g ≠ 0) (x : ℝ) :
    (bias μ g hmass x : ℝ) =
      (∫⁻ t in Iio x, AcceptedProposal.weight g t ∂μ).toReal /
        (AcceptedProposal.mass μ g).toReal := by
  simp only [bias, BooleanEvent.bias, Subtype.coe_mk, Measure.real, event_preimage,
    AcceptedProposal.law, Measure.smul_apply, withDensity_apply _ measurableSet_Iio,
    smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]
  ring

/-- The accepted event receives its credit; rejection restarts with amplified slack. -/
def kernel (hmass : AcceptedProposal.mass μ g ≠ 0) (x : ℝ)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  AcceptedProposal.kernel μ g hmass (fun y => F (event x y)) ε t

omit [IsProbabilityMeasure μ] in
theorem measurable_kernel (hg : Measurable g) (hmass : AcceptedProposal.mass μ g ≠ 0)
    (x : ℝ) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) : Measurable (kernel μ g hmass x F ε) :=
  AcceptedProposal.measurable_kernel μ g hg hmass (fun t => F (event x t))
    ((measurable_of_countable F).comp (measurable_event x)) ε

/-- Acceptance normalization and the Boolean observation preserve every continuation credit. -/
theorem expectation_preservation (hg : Measurable g)
    (hmass : AcceptedProposal.mass μ g ≠ 0) (x : ℝ) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ t, kernel μ g hmass x F ε t ∂μ ≤ RealCoin.credit (bias μ g hmass x) F + ε := by
  simpa only [kernel, AcceptedProposal.credit, credit_eq] using
    AcceptedProposal.expectation_preservation μ g hg hmass (fun t => F (event x t))
      ((measurable_of_countable F).comp (measurable_event x)) ε

end

end SampLib.ThresholdRejection
