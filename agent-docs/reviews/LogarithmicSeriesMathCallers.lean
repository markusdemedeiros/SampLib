import SampLib.Discrete.Laws.LogarithmicSeries

open MeasureTheory SampLib LogarithmicSeries
open scoped ENNReal

noncomputable section

variable (p : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)

example : law p hp hp1 Set.univ = 1 := by simp

example : law p hp hp1 {1} = ENNReal.ofReal ((p : ℝ) / normalizer p) := by
  simpa using law_succ p hp hp1 0

example : (∫⁻ _ : ℕ, (∞ : ℝ≥0∞) ∂law p hp hp1) = ∞ := by simp

example : (∫⁻ n, (if n = 0 then ∞ else 7 : ℝ≥0∞) ∂law p hp hp1) = 7 := by
  have hs : ∀ᵐ n ∂law p hp hp1, n ≠ 0 := by
    rw [ae_iff]
    simpa using law_zero p hp hp1
  calc
    _ = ∫⁻ _ : ℕ, (7 : ℝ≥0∞) ∂law p hp hp1 :=
      lintegral_congr_ae (hs.mono fun n hn => ite_eq_right hn)
    _ = 7 := by simp

#print axioms mass_eq
#print axioms mass_pos
#print axioms law_succ
#print axioms expectation
