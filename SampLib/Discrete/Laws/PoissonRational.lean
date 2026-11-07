import SampLib.Uniform.Laws.RationalCoin
import SampLib.Common.Laws.Binomial
import SampLib.Common.Laws.PoissonThinning

/-! # Rational-rate Poisson credit

Whole unit rates add independent Poisson counts. The fractional rate thins one
further count. Both branches give the same Poisson expectation.
-/

open scoped ENNReal NNReal

namespace SampLib.PoissonRational

noncomputable section

open MeasureTheory

def rate (x y : ℕ) : ℝ≥0 := (x : ℝ≥0) / y

def bias (x y : ℕ) (hy : 0 < y) (hxy : x ≤ y) : unitInterval :=
  RationalCoin.bias x y (Int.natCast_nonneg _) (Int.natCast_pos.mpr hy)
    (Int.ofNat_le.mpr hxy)

theorem rate_split (x y : ℕ) (hy : 0 < y) (hxy : y ≤ x) :
    rate x y = 1 + rate (x - y) y := by
  unfold rate
  have hy' : (y : ℝ≥0) ≠ 0 := by exact_mod_cast hy.ne'
  conv_lhs => rw [← Nat.add_sub_of_le hxy]
  rw [Nat.cast_add, add_div, div_self hy']

theorem bias_rate (x y : ℕ) (hy : 0 < y) (hxy : x ≤ y) :
    unitInterval.toNNReal (bias x y hy hxy) = rate x y := by
  apply NNReal.coe_injective
  simp [bias, rate, RationalCoin.bias]

def credit (x y total : ℕ) (F : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ k, F (total + k) ∂ProbabilityTheory.poissonMeasure (rate x y)

@[simp] theorem credit_zero (y total : ℕ) (F : ℕ → ℝ≥0∞) :
    credit 0 y total F = F total := by
  simp [credit, rate, Distributions.poissonMeasure_zero]

def drawCredit (x y total : ℕ) (hy : 0 < y) (F : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  if h : y ≤ x then credit (x - y) y (total + n) F
  else ∫⁻ k, F (total + k)
    ∂Binomial.law (bias x y hy (Nat.le_of_lt (Nat.lt_of_not_ge h))) n

/-- Additivity and thinning identify both branches with the requested remaining rate. -/
theorem expectation (x y total : ℕ) (hy : 0 < y) (F : ℕ → ℝ≥0∞) :
    (∫⁻ n, drawCredit x y total hy F n ∂ProbabilityTheory.poissonMeasure 1) =
      credit x y total F := by
  by_cases hxy : y ≤ x
  · simp only [drawCredit, dite_eq_left hxy, credit, Nat.add_assoc]
    simpa only [Nat.add_assoc, ← rate_split x y hy hxy] using
      Distributions.lintegral_poisson_add 1 (rate (x - y) y) (fun z => F (total + z))
  · simp only [drawCredit, dite_eq_right hxy]
    simp_rw [Binomial.law_eq_binomial]
    rw [← Measure.lintegral_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable,
      Distributions.poissonMeasure_bind_binomial, one_mul, bias_rate]
    rfl

end

end SampLib.PoissonRational
