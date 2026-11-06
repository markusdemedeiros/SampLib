module

public import SampLib.PSRN.Laws.GammaSuccessor

@[expose] public section

/-! # Natural-shape gamma sums, with an explicit empty sum

The zero-fold sum is `dirac 0`, independently of mathlib's gamma density at shape
zero. Positive natural shapes agree with the normalized gamma distribution.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory

namespace SampLib.GammaErlang

noncomputable section

/-- The analytic law of an `n`-fold exponential sum, including its empty sum. -/
def law (rate : ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => gammaMeasure ((n + 1 : ℕ) : ℝ) rate

@[simp] theorem law_zero (rate : ℝ) : law rate 0 = Measure.dirac 0 := rfl

/-- Positive natural shape agrees with the ordinary gamma measure. -/
theorem law_eq_gamma (rate : ℝ) (n : ℕ) (hn : 0 < n) :
    law rate n = gammaMeasure (n : ℝ) rate := by cases n <;> simp_all [law]

theorem probability (rate : ℝ) (hrate : 0 < rate) (n : ℕ) :
    IsProbabilityMeasure (law rate n) := by
  cases n with
  | zero => simp only [law]; infer_instance
  | succ n => exact isProbabilityMeasure_gammaMeasure (by positivity) hrate

/-- Mathlib's exponential law is its shape-one gamma law. -/
theorem exponential_eq_gamma (rate : ℝ) : expMeasure rate = gammaMeasure 1 rate := by
  rw [expMeasure]

/-- Appending one independent exponential increments the natural shape. -/
theorem convolution_step (rate : ℝ) (hrate : 0 < rate) (n : ℕ) :
    law rate n ∗ expMeasure rate = law rate (n + 1) := by
  let := isProbabilityMeasure_expMeasure hrate
  cases n with
  | zero =>
    simp only [law]
    rw [Measure.dirac_conv]
    simp only [zero_add, Measure.map_id', Nat.cast_one]
    rw [expMeasure]
  | succ n =>
    simpa only [law, Nat.cast_add, Nat.cast_one, add_assoc] using
      GammaSuccessor.gamma_conv_exponential ((n + 1 : ℕ) : ℝ) rate (by positivity) hrate

/-- A positive real shape and a natural shape add without a shape-zero density convention. -/
theorem gamma_conv_erlang (shape rate : ℝ) (hshape : 0 < shape) (hrate : 0 < rate) (n : ℕ) :
    gammaMeasure shape rate ∗ law rate n = gammaMeasure (shape + n) rate := by
  let := isProbabilityMeasure_gammaMeasure hshape hrate
  let := isProbabilityMeasure_expMeasure hrate
  induction n with
  | zero => simp [law, Measure.conv_dirac]
  | succ n IH =>
    let := probability rate hrate n
    rw [← convolution_step rate hrate n, ← Measure.conv_assoc, IH,
      GammaSuccessor.gamma_conv_exponential (shape + n) rate (by positivity) hrate]
    congr 1
    push_cast
    ring

/-- Convolution adds any two natural shapes, including either empty sum. -/
theorem convolution_add (rate : ℝ) (hrate : 0 < rate) (m n : ℕ) :
    law rate m ∗ law rate n = law rate (m + n) := by
  let := probability rate hrate m
  let := isProbabilityMeasure_expMeasure hrate
  induction n with
  | zero =>
    change law rate m ∗ Measure.dirac 0 = law rate m
    rw [Measure.conv_dirac]
    simp
  | succ n IH =>
    let := probability rate hrate n
    rw [← convolution_step rate hrate n, ← Measure.conv_assoc, IH,
      convolution_step rate hrate (m + n)]
    rfl

/-- Natural-shape sum expectations for arbitrary ENNReal continuation credits. -/
theorem expectation (rate : ℝ) (hrate : 0 < rate) (m n : ℕ)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, ∫⁻ y, F (x + y) ∂law rate n ∂law rate m) =
      ∫⁻ z, F z ∂law rate (m + n) := by
  let := probability rate hrate m
  let := probability rate hrate n
  rw [← Measure.lintegral_conv hF, convolution_add rate hrate m n]

/-- Positive real plus natural shape, also for unbounded and infinite credits. -/
theorem gamma_expectation (shape rate : ℝ) (hshape : 0 < shape) (hrate : 0 < rate) (n : ℕ)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, ∫⁻ y, F (x + y) ∂law rate n ∂gammaMeasure shape rate) =
      ∫⁻ z, F z ∂gammaMeasure (shape + n) rate := by
  let := probability rate hrate n
  let := isProbabilityMeasure_gammaMeasure hshape hrate
  rw [← Measure.lintegral_conv hF, gamma_conv_erlang shape rate hshape hrate n]

end

end SampLib.GammaErlang
