import SampLib.Discrete.Laws.Geometric
import SampLib.Bernoulli.Laws.OneDivOnePlus

/-! # Two-sided geometric law

A geometric magnitude takes either its nonnegative position or the matching
negative position. The reciprocal selector balances the two tails.
-/

open scoped ENNReal

namespace SampLib.SymmetricGeometric

noncomputable section

open MeasureTheory

/-- Place a geometric count on the selected side of zero. -/
def signed (n : ℕ) (b : Bool) : ℤ := if b then n else -1 - (n : ℤ)

/-- The two-sided law, including its degenerate limit at success probability one. -/
def law (p : unitInterval) : Measure ℤ :=
  ((Geometric.law p).prod (OneDivOnePlus.law (unitInterval.symm p))).map
    (fun z => signed z.1 z.2)

instance (p : unitInterval) : IsProbabilityMeasure (law p) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Each nonnegative atom is a geometric atom times the positive-side mass. -/
theorem law_nonneg (p : unitInterval) (n : ℕ) :
    law p {(n : ℤ)} = Geometric.law p {n} *
      OneDivOnePlus.law (unitInterval.symm p) {true} := by
  have hpre : (fun z : ℕ × Bool => signed z.1 z.2) ⁻¹' {(n : ℤ)} =
      ({n} : Set ℕ) ×ˢ {true} := by
    ext ⟨k, b⟩
    cases b <;> simp [signed]; omega
  rw [law, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    hpre, Measure.prod_prod]

/-- Negative atoms form the other geometric tail, shifted one place below zero. -/
theorem law_neg (p : unitInterval) (n : ℕ) :
    law p {-1 - (n : ℤ)} = Geometric.law p {n} *
      OneDivOnePlus.law (unitInterval.symm p) {false} := by
  have hpre : (fun z : ℕ × Bool => signed z.1 z.2) ⁻¹' {-1 - (n : ℤ)} =
      ({n} : Set ℕ) ×ˢ {false} := by
    ext ⟨k, b⟩
    cases b <;> simp [signed]; omega
  rw [law, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    hpre, Measure.prod_prod]

private theorem side_true (p : unitInterval) :
    OneDivOnePlus.law (unitInterval.symm p) {true} =
      ENNReal.ofReal (1 / (2 - (p : ℝ))) := by
  simp [OneDivOnePlus.law, RealCoin.law, RealCoin.pmf, OneDivOnePlus.bias,
    EvenParity.bias, unitInterval.coe_symm_eq,
    show 1 + (1 - (p : ℝ)) = 2 - (p : ℝ) by ring]

private theorem side_false (p : unitInterval) :
    OneDivOnePlus.law (unitInterval.symm p) {false} =
      ENNReal.ofReal ((1 - (p : ℝ)) / (2 - (p : ℝ))) := by
  have hd : (0 : ℝ) < 2 - (p : ℝ) := by linarith [p.2.2]
  have he : 1 - 1 / (2 - (p : ℝ)) = (1 - (p : ℝ)) / (2 - (p : ℝ)) := by
    field_simp
    ring
  simp [OneDivOnePlus.law, RealCoin.law, RealCoin.pmf, OneDivOnePlus.bias,
    EvenParity.bias, unitInterval.coe_symm_eq,
    show 1 + (1 - (p : ℝ)) = 2 - (p : ℝ) by ring]
  exact congrArg ENNReal.ofReal (by simpa only [one_div] using he)

/-- The nonnegative tail has the standard normalized two-sided geometric mass. -/
theorem nonneg_mass (p : unitInterval) (hp : 0 < (p : ℝ)) (n : ℕ) :
    law p {(n : ℤ)} = ENNReal.ofReal ((1 - (p : ℝ)) ^ n * p / (2 - (p : ℝ))) := by
  have hpne : p ≠ 0 := by intro he; simp [he] at hp
  rw [law_nonneg, ProbabilityTheory.geometricMeasure_singleton hpne, side_true,
    ← ENNReal.ofReal_mul (ProbabilityTheory.geometricMeasure_nonneg p n)]
  congr 1
  ring

/-- The negative tail has exactly the same mass as its reflection about zero. -/
theorem neg_mass (p : unitInterval) (hp : 0 < (p : ℝ)) (n : ℕ) :
    law p {-1 - (n : ℤ)} =
      ENNReal.ofReal ((1 - (p : ℝ)) ^ (n + 1) * p / (2 - (p : ℝ))) := by
  have hpne : p ≠ 0 := by intro he; simp [he] at hp
  rw [law_neg, ProbabilityTheory.geometricMeasure_singleton hpne, side_false,
    ← ENNReal.ofReal_mul (ProbabilityTheory.geometricMeasure_nonneg p n)]
  congr 1
  rw [pow_succ]
  ring

/-- Conditional signed expectation after observing the geometric magnitude. -/
def continuation (p : unitInterval) (F : ℤ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ b, F (signed n b) ∂OneDivOnePlus.law (unitInterval.symm p)

/-- Independent magnitude and side give the signed product expectation. -/
theorem expectation (p : unitInterval) (F : ℤ → ℝ≥0∞) :
    ∫⁻ n, continuation p F n ∂Geometric.law p = ∫⁻ z, F z ∂law p := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]
  rfl

end

end SampLib.SymmetricGeometric
