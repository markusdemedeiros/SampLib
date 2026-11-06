module

public import Metrology.ProbLang.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

@[expose] public section

/-! # Uniform law on a finite range of naturals -/

open Set Finset
open scoped ENNReal

namespace SampLib.UniformInt

noncomputable section

open MeasureTheory Measure

/-- Uniform law on the integers represented by `0, …, n-1`. -/
def law (n : ℕ) : Measure ℕ := uniformOfFinset (range n)

instance (n : ℕ) [NeZero n] : IsProbabilityMeasure (law n) :=
  isProbabilityMeasure_uniformOfFinset (nonempty_range_iff.mpr (NeZero.ne n))

/-- Uniform continuation credit is the arithmetic mean over the range. -/
theorem lintegral_law (n : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, F k ∂law n = (∑ k ∈ range n, F k) / n := by
  simp only [law, uniformOfFinset, lintegral_finsetSum_measure,
    lintegral_smul_measure, lintegral_dirac, smul_eq_mul, card_range]
  rw [← mul_sum, ENNReal.div_eq_inv_mul]

/-- Uniform ranks lie in their finite range, including the empty zero measure. -/
theorem ae_lt (n : ℕ) : ∀ᵐ k ∂law n, k < n := by
  apply ae_iff_of_countable.mpr
  intro k hk
  by_contra h
  apply hk
  simp [law, uniformOfFinset_apply_singleton, Finset.mem_range, h]

end

end SampLib.UniformInt
