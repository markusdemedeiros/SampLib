import SampLib.Continuous.Laws.Mixture
import SampLib.Discrete.Laws.BinomialBinary
import SampLib.Uniform.Laws.UniformInt
import SampLib.Uniform.Laws.RationalCoin

/-! # CUB law

The CUB law mixes one plus a binomial count with a uniform category. A response
expectation is the mixture of the two shifted component expectations.
-/

open scoped ENNReal

namespace SampLib.Cub

noncomputable section

open MeasureTheory

/-- The standard combination of uniform and shifted-binomial responses. -/
def law (m : ℕ) (p ξ : unitInterval) : Measure ℕ :=
  (Mixture.law p (Binomial.law (unitInterval.symm ξ) (m - 1))
    (UniformInt.law (m - 1 + 1))).map Nat.succ

instance (m : ℕ) (p ξ : unitInterval) : IsProbabilityMeasure (law m p ξ) := by
  unfold law
  infer_instance

/-- A response expectation is the mixture of its two shifted component expectations. -/
theorem expectation (m : ℕ) (p ξ : unitInterval) (hm : 0 < m)
    (F : ℕ → ℝ≥0∞) :
    (∫⁻ k, F k ∂law m p ξ) = RealCoin.credit p
      (fun b => if b then ∫⁻ k, F (k + 1) ∂Binomial.law (unitInterval.symm ξ) (m - 1)
        else ∫⁻ k, F (k + 1) ∂UniformInt.law m) := by
  rw [law, Nat.sub_add_cancel (by omega : 1 ≤ m),
    lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    Mixture.expectation_preservation]

theorem rational_bias (a b : ℕ) (hb : 0 < b) (ha : a ≤ b) :
    RationalCoin.bias a b (by omega) (by omega) (by omega) = BinomialBinary.bias a b := by
  apply Subtype.ext
  rw [BinomialBinary.bias_coe a b hb ha]
  simp [RationalCoin.bias]

theorem complement_bias (a b : ℕ) (hb : 0 < b) (ha : a ≤ b) :
    BinomialBinary.bias (b - a) b = unitInterval.symm (BinomialBinary.bias a b) := by
  apply Subtype.ext
  rw [BinomialBinary.bias_coe (b - a) b hb (by omega), unitInterval.coe_symm_eq,
    BinomialBinary.bias_coe a b hb ha, Nat.cast_sub ha]
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  field_simp

end

end SampLib.Cub
