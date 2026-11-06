import SampLib.Distributions.Metropolis
import SampLib.CappedRationalCoin

/-! # A proposal kernel with exact rational acceptance ratios

Separating the proposal law from the ratio representation covers both normalized
Hastings probabilities and the constant ratio used for symmetric proposals.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace SampLib.MetropolisRatio

noncomputable section

variable {α : Type _}

/-- A positive-denominator representation of the directed proposal ratios. -/
structure Ratios (α : Type _) where
  numerator : α → α → ℕ
  denominator : α → α → ℕ
  denominator_pos : ∀ x y, 0 < denominator x y

def weight (r : Ratios α) (x y : α) : ℝ≥0 :=
  (r.numerator x y : ℝ≥0) / r.denominator x y

def numerator (w : α → ℕ) (r : Ratios α) (x y : α) : ℕ :=
  w y * r.numerator y x * r.denominator x y

def denominator (w : α → ℕ) (r : Ratios α) (x y : α) : ℕ :=
  w x * r.numerator x y * r.denominator y x

theorem denominator_pos (w : α → ℕ) (r : Ratios α) (x y : α)
    (hx : 0 < w x) (hy : 0 < r.numerator x y) : 0 < denominator w r x y :=
  mul_pos (mul_pos hx hy) (r.denominator_pos y x)

/-- Clearing proposal denominators gives precisely the implemented integer ratio. -/
theorem bias_eq (w : α → ℕ) (r : Ratios α) (x y : α)
    (hx : 0 < w x) (hy : 0 < r.numerator x y) :
    Metropolis.bias (fun x => (w x : ℝ≥0)) (weight r) x y =
      CappedRationalCoin.bias (numerator w r x y) (denominator w r x y)
        (by positivity) (by exact_mod_cast denominator_pos w r x y hx hy) := by
  apply Subtype.ext
  have hxR : (0 : ℝ) < w x := by exact_mod_cast hx
  have hyR : (0 : ℝ) < r.numerator x y := by exact_mod_cast hy
  have hf : (0 : ℝ) < r.denominator x y := by exact_mod_cast r.denominator_pos x y
  have hr : (0 : ℝ) < r.denominator y x := by exact_mod_cast r.denominator_pos y x
  simp only [Metropolis.bias, Metropolis.acceptance, weight, NNReal.coe_div,
    NNReal.coe_min, NNReal.coe_mul, NNReal.coe_natCast, CappedRationalCoin.bias]
  rw [← min_div_div_right (by positivity : (0 : ℝ) ≤ w x * (r.numerator x y / r.denominator x y)),
    div_self (by positivity : (w x : ℝ) * (r.numerator x y / r.denominator x y) ≠ 0)]
  congr 1
  simp only [numerator, denominator, Nat.cast_mul]
  push_cast
  field_simp

/-- A zero-target candidate is rejected with probability one. -/
theorem accept_support (w : α → ℕ) (r : Ratios α) (x y : α) :
    ∀ᵐ b ∂RealCoin.law (Metropolis.bias (fun x => (w x : ℝ≥0)) (weight r) x y),
      b = true → 0 < w y := by
  apply ae_iff_of_countable.mpr
  intro b hb
  cases b with
  | false => simp
  | true =>
    intro _
    by_contra h
    apply hb
    simp [RealCoin.law, RealCoin.pmf, Metropolis.bias, Metropolis.acceptance,
      Nat.eq_zero_of_not_pos h]

section kernel

variable [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

/-- Acceptance selects the proposed state; rejection retains the current one. -/
def selection (w : α → ℕ) (r : Ratios α) (x y : α) : Measure α :=
  (RealCoin.pmf (Metropolis.bias (fun x => (w x : ℝ≥0)) (weight r) x y) true •
    Measure.dirac y) +
  (RealCoin.pmf (Metropolis.bias (fun x => (w x : ℝ≥0)) (weight r) x y) false •
    Measure.dirac x)

instance (w : α → ℕ) (r : Ratios α) (x y : α) :
    IsProbabilityMeasure (selection w r x y) where
  measure_univ := by
    simpa [selection] using RealCoin.pmf_sum
      (Metropolis.bias (fun x => (w x : ℝ≥0)) (weight r) x y)

def kernel (w : α → ℕ) (r : Ratios α) (μ : α → Measure α) (x : α) : Measure α :=
  (μ x).bind (selection w r x)

instance (w : α → ℕ) (r : Ratios α) (μ : α → Measure α)
    [∀ x, IsProbabilityMeasure (μ x)] (x : α) : IsProbabilityMeasure (kernel w r μ x) where
  measure_univ := by
    rw [kernel, Measure.bind_apply MeasurableSet.univ
      (measurable_of_countable _).aemeasurable]
    simp

abbrev law (w : α → ℕ) (r : Ratios α) (μ : α → Measure α) :=
  FiniteKernels.iterate (kernel w r μ)

/-- First condition on the proposal, then on acceptance. -/
theorem expectation (w : α → ℕ) (r : Ratios α) (μ : α → Measure α)
    (n : ℕ) (x : α) (F : α → ℝ≥0∞) :
    ∫⁻ y, RealCoin.credit (Metropolis.bias (fun x => (w x : ℝ≥0)) (weight r) x y)
      (fun b => ∫⁻ z, F z ∂law w r μ n (if b then y else x)) ∂μ x =
      ∫⁻ z, F z ∂law w r μ (n + 1) x := by
  rw [← FiniteKernels.expectation]
  simp only [kernel,
    Measure.lintegral_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable]
  congr 1
  funext y
  simp [selection, RealCoin.credit, smul_eq_mul]

end kernel

end

end SampLib.MetropolisRatio
