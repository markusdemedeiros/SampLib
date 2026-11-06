import SampLib.Discrete.BoundedGeometric
import SampLib.Uniform.UniformInt
import SampLib.Uniform.FairCoin

/-! # Truncated binary-format uniforms

A capped fair-geometric leading-zero count is independent of a uniform mantissa.
At the cap, the represented pair is zero. Otherwise it is the leading one and
mantissa, scaled by the corresponding negative binary exponent.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.UniformBinaryFloat

noncomputable section

private instance pow_neZero (precision : ℕ) : NeZero (2 ^ precision) := ⟨by positivity⟩

/-- The integer significand/exponent pair for a nonzero result. -/
def point (precision zeros mantissa : ℕ) : ℤ × ℤ :=
  (((2 ^ precision + mantissa : ℕ) : ℤ), -((zeros + precision + 1 : ℕ) : ℤ))

/-- Decode the independent leading-zero and mantissa draws, truncating at the cap. -/
def decode (precision cap offset zeros mantissa : ℕ) : ℤ × ℤ :=
  if zeros = cap then (0, 0) else point precision (offset + zeros) mantissa

/-- The joint product law, decoded after an already-read zero prefix. -/
def lawFrom (precision cap offset : ℕ) : Measure (ℤ × ℤ) :=
  ((BoundedGeometric.law VonNeumann.fairBias cap).prod
    (UniformInt.law (2 ^ precision))).map (fun zm => decode precision cap offset zm.1 zm.2)

instance (precision cap offset : ℕ) : IsProbabilityMeasure (lawFrom precision cap offset) where
  measure_univ := by
    rw [lawFrom, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- The exact finite-format output law, including zero precision and zero cap. -/
abbrev law (precision cap : ℕ) := lawFrom precision cap 0

@[simp] theorem lawFrom_zero (precision offset : ℕ) :
    lawFrom precision 0 offset = Measure.dirac (0, 0) := by
  rw [lawFrom, BoundedGeometric.law, Measure.dirac_prod,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  simp [Function.comp_def, decode]

/-- Expected continuation credit at a fixed zero prefix. -/
def credit (precision cap offset : ℕ) (F : ℤ × ℤ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x, F x ∂lawFrom precision cap offset

private theorem credit_product (precision cap offset : ℕ) (F : ℤ × ℤ → ℝ≥0∞) :
    credit precision cap offset F =
      ∫⁻ z, ∫⁻ m, F (decode precision cap offset z m) ∂UniformInt.law (2 ^ precision)
        ∂BoundedGeometric.law VonNeumann.fairBias cap := by
  rw [credit, lawFrom, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]

@[simp] theorem credit_zero (precision offset : ℕ) (F : ℤ × ℤ → ℝ≥0∞) :
    credit precision 0 offset F = F (0, 0) := by simp [credit]

private theorem decode_succ (precision cap offset z m : ℕ) :
    decode precision (cap + 1) offset (z + 1) m = decode precision cap (offset + 1) z m := by
  by_cases hz : z = cap
  · simp [decode, hz]
  · simp [decode, hz, point, Nat.add_left_comm, Nat.add_comm]

/-- Credit after the next bit: read the mantissa or advance the zero prefix. -/
def coinCredit (precision cap offset : ℕ) (F : ℤ × ℤ → ℝ≥0∞) : Bool → ℝ≥0∞
  | true => ∫⁻ m, F (point precision offset m) ∂UniformInt.law (2 ^ precision)
  | false => credit precision cap (offset + 1) F

/-- Fubini and the capped-geometric split preserve the independent product expectation. -/
theorem expectation (precision cap offset : ℕ) (F : ℤ × ℤ → ℝ≥0∞) :
    ∫⁻ b, coinCredit precision cap offset F b ∂RealCoin.law VonNeumann.fairBias =
      credit precision (cap + 1) offset F := by
  rw [credit_product precision (cap + 1) offset F,
    ← BoundedGeometric.expectation VonNeumann.fairBias cap
      (fun z => ∫⁻ m, F (decode precision (cap + 1) offset z m)
        ∂UniformInt.law (2 ^ precision))]
  apply lintegral_congr
  intro b
  cases b with
  | false =>
    simp only [coinCredit, BoundedGeometric.continuation, Bool.false_eq_true, ite_false]
    rw [credit_product]
    simp_rw [decode_succ]
  | true => simp [coinCredit, BoundedGeometric.continuation, decode]

end

end SampLib.UniformBinaryFloat
