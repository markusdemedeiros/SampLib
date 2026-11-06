import SampLib.Bernoulli.Laws.Linear2014Escape

/-! # The complete jump law of one expanding-factory step

A true input moves one level down. A false input adds an independent geometric
jump. The named probability law collects these two samplings for the stage's
harmonic and termination arguments.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SampLib.Linear2014Jump

noncomputable section

/-- The next natural state after the input trial and optional geometric jump. -/
def law (p q : unitInterval) (s : ℕ) : Measure ℕ :=
  (RealCoin.pmf p true • Measure.dirac (s - 1)) +
    (RealCoin.pmf p false • (geometricMeasure q).map (fun n => s + n))

instance (p q : unitInterval) (s : ℕ) : IsProbabilityMeasure (law p q s) where
  measure_univ := by simpa [law] using RealCoin.pmf_sum p

/-- Integrating the named law is exactly the source's nested sampling expectation. -/
theorem lintegral_law (p q : unitInterval) (s : ℕ) (H : ℕ → ℝ≥0∞) :
    (∫⁻ n, H n ∂law p q s) =
      ∫⁻ a, if a then H (s - 1) else ∫⁻ n, H (s + n) ∂geometricMeasure q
        ∂RealCoin.law p := by
  rw [RealCoin.lintegral_law]
  simp [law, RealCoin.credit, lintegral_map (measurable_of_countable _)
    (measurable_of_countable _), smul_eq_mul]

/-- The source's complete jump law preserves every harmonic continuation credit. -/
theorem credit_expectation (p q t : unitInterval) (hq : 0 < (q : ℝ))
    (hrelation : (1 - (q : ℝ)) * t = p) (s : ℕ) (hs : 0 < s) (F : Bool → ℝ≥0∞) :
    (∫⁻ n, IterateCoin.credit t n F ∂law p q s) = IterateCoin.credit t s F := by
  rw [lintegral_law]
  exact jump_expectation p q t hq hrelation s hs F

/-- Every stage has the same escape lower bound at all of its ordinary states. -/
theorem ordinary_bound (p q : unitInterval) (hq : 0 < (q : ℝ))
    (N D s : ℕ) (hD : 0 < D) :
    (∫⁻ n, ordinary N D n ∂law p q s) ≤ ENNReal.ofReal (1 - escape p q N) := by
  rw [lintegral_law]
  exact ordinary_expectation_le p q hq N D s hD

end

end SampLib.Linear2014Jump
