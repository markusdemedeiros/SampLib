import SampLib.Discrete.Laws.DyadicBlocks
import SampLib.Discrete.Laws.Geometric
import SampLib.Discrete.Laws.UniformFin

/-! # A geometric choice of dyadic block, followed by a uniform rank -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.DyadicProposal

noncomputable section

open DyadicBlocks

/-- The finite rank retains its chosen level in the joint output. -/
def fibreLaw (l : ℕ) : Measure Block :=
  (UniformFin.law (2 ^ l)).map (Sigma.mk l)

instance (l : ℕ) : IsProbabilityMeasure (fibreLaw l) := by
  have : NeZero (2 ^ l) := ⟨by positivity⟩
  unfold fibreLaw
  infer_instance

/-- Geometric levels with independent uniform ranks. -/
def law (p : unitInterval) : Measure Block :=
  (Geometric.law p).bind fibreLaw

instance (p : unitInterval) : IsProbabilityMeasure (law p) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
    simp

/-- Joint expectations are exactly the two source draws in order. -/
theorem lintegral_law (p : unitInterval) (F : Block → ℝ≥0∞) :
    ∫⁻ t, F t ∂law p =
      ∫⁻ l, ∫⁻ r, F ⟨l, r⟩ ∂UniformFin.law (2 ^ l) ∂Geometric.law p := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]
  apply lintegral_congr
  intro l
  rw [fibreLaw, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

theorem fibre_singleton (l : ℕ) (t : Block) :
    fibreLaw l {t} = if l = t.1 then (2 ^ l : ℝ≥0∞)⁻¹ else 0 := by
  obtain ⟨k, r⟩ := t
  rw [fibreLaw, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  by_cases h : l = k
  · subst k
    have hpre : (fun x : Fin (2 ^ l) => (⟨l, x⟩ : Block)) ⁻¹' {⟨l, r⟩} = {r} := by
      ext x
      simp
    rw [hpre, UniformFin.law_singleton]
    simp
  · have hpre : (fun x : Fin (2 ^ l) => (⟨l, x⟩ : Block)) ⁻¹' {⟨k, r⟩} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact fun heq => h (congrArg Sigma.fst heq)
    rw [hpre]
    simp [h]

/-- The rank contributes its reciprocal block width to the geometric point mass. -/
theorem law_singleton (p : unitInterval) (hp : p ≠ 0) (t : Block) :
    law p {t} = ENNReal.ofReal ((1 - (p : ℝ)) ^ t.1 * p) / (2 ^ t.1 : ℝ≥0∞) := by
  rw [law, Measure.bind_apply (measurableSet_singleton _) (measurable_of_countable _).aemeasurable]
  simp_rw [fibre_singleton]
  rw [lintegral_countable', tsum_eq_single t.1]
  · rw [ite_eq_left rfl, ProbabilityTheory.geometricMeasure_singleton hp,
      ENNReal.div_eq_inv_mul]
  · intro l hl
    simp [hl]

/-- The same point mass expressed entirely in nonnegative real coefficients. -/
theorem law_singleton_ofReal (p : unitInterval) (hp : p ≠ 0) (t : Block) :
    law p {t} = ENNReal.ofReal (((1 - (p : ℝ)) ^ t.1 * p) / (2 : ℝ) ^ t.1) := by
  rw [law_singleton p hp, ENNReal.ofReal_div_of_pos (by positivity)]
  simp

end

end SampLib.DyadicProposal
