import SampLib.Uniform.Laws.RealCoin

/-! # Marginal law of a measurable conditional Bernoulli coin -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.ConditionalCoin

noncomputable section

variable {Ω : Type} [MeasurableSpace Ω]

/-- Average the two conditional masses, retaining an ordinary Boolean output law. -/
def mass (μ : Measure Ω) (φ : Ω → unitInterval) (b : Bool) : ℝ≥0∞ :=
  ∫⁻ x, RealCoin.pmf (φ x) b ∂μ

def law (μ : Measure Ω) (φ : Ω → unitInterval) : Measure Bool :=
  (mass μ φ true • Measure.dirac true) + (mass μ φ false • Measure.dirac false)

theorem measurable_pmf {φ : Ω → unitInterval} (hφ : Measurable φ) (b : Bool) :
    Measurable (fun x => RealCoin.pmf (φ x) b) := by
  cases b <;> simp only [RealCoin.pmf, Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

theorem mass_sum (μ : Measure Ω) [IsProbabilityMeasure μ] (φ : Ω → unitInterval)
    (hφ : Measurable φ) : mass μ φ true + mass μ φ false = 1 := by
  rw [mass, mass, ← lintegral_add_left (measurable_pmf hφ true)]
  simp [RealCoin.pmf_sum]

instance (μ : Measure Ω) [IsProbabilityMeasure μ] (φ : Ω → unitInterval)
    [hφ : Fact (Measurable φ)] : IsProbabilityMeasure (law μ φ) where
  measure_univ := by simpa [law] using mass_sum μ φ hφ.out

/-- Arbitrary, possibly infinite output credit commutes with marginalization. -/
theorem lintegral_law (μ : Measure Ω) (φ : Ω → unitInterval) (hφ : Measurable φ)
    (F : Bool → ℝ≥0∞) :
    (∫⁻ b, F b ∂law μ φ) = ∫⁻ x, RealCoin.credit (φ x) F ∂μ := by
  simp only [law, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac,
    smul_eq_mul]
  unfold RealCoin.credit mass
  have ht : Measurable (fun x => RealCoin.pmf (φ x) true * F true) :=
    (measurable_pmf hφ true).mul measurable_const
  rw [lintegral_add_left ht,
    lintegral_mul_const _ (measurable_pmf hφ true),
    lintegral_mul_const _ (measurable_pmf hφ false)]

/-- A normalized Boolean mixture is determined by its true mass. -/
theorem law_eq_coin (μ : Measure Ω) [IsProbabilityMeasure μ] (φ : Ω → unitInterval)
    (hφ : Measurable φ) (p : unitInterval)
    (htrue : mass μ φ true = ENNReal.ofReal (p : ℝ)) : law μ φ = RealCoin.law p := by
  have ht : mass μ φ true = RealCoin.pmf p true := by
    simpa only [RealCoin.pmf, ite_true] using htrue
  have hf : mass μ φ false = RealCoin.pmf p false := by
    apply (ENNReal.add_right_inj (by simp [RealCoin.pmf] : RealCoin.pmf p true ≠ ∞)).mp
    rw [← ht, mass_sum μ φ hφ, ht, RealCoin.pmf_sum]
  simp only [law, RealCoin.law, ht, hf]

end

end SampLib.ConditionalCoin
