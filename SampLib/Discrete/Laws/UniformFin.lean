import SampLib.Uniform.Laws.UniformInt

/-! # Uniform law on a finite range -/

open Finset
open scoped ENNReal

namespace SampLib.UniformFin

noncomputable section

open MeasureTheory Measure

/-- The bound is retained in the mathematical output type. -/
def law (n : ℕ) : Measure (Fin n) := uniformOfFinset univ

instance (n : ℕ) [NeZero n] : IsProbabilityMeasure (law n) :=
  isProbabilityMeasure_uniformOfFinset Finset.univ_nonempty

theorem lintegral_law (n : ℕ) (F : Fin n → ℝ≥0∞) :
    ∫⁻ k, F k ∂law n = (∑ k, F k) / n := by
  simp only [law, uniformOfFinset, lintegral_finsetSum_measure,
    lintegral_smul_measure, lintegral_dirac, smul_eq_mul, card_univ, Fintype.card_fin]
  rw [← mul_sum, ENNReal.div_eq_inv_mul]

theorem law_singleton (n : ℕ) (k : Fin n) : law n {k} = (n : ℝ≥0∞)⁻¹ := by
  simp [law, uniformOfFinset_apply_singleton]

end

end SampLib.UniformFin
