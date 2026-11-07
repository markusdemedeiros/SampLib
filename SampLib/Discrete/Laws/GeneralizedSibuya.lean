import SampLib.Discrete.Laws.InverseUrnOne

/-! # Generalized Sibuya law

After clearing denominators, the reciprocal hazards are first-marked urn hazards.
The law is one plus the first-marked waiting count, with a rising-product mass.
-/

open scoped ENNReal

namespace SampLib.GeneralizedSibuya

noncomputable section

open MeasureTheory (Measure IsProbabilityMeasure lintegral_map)

/-- Source domain: alpha>0, nu>=0 and alpha<nu+1, represented by rational pairs. -/
structure Parameters where
  alphaNumerator : ℕ
  alphaDenominator : ℕ
  nuNumerator : ℕ
  nuDenominator : ℕ
  alphaNumerator_pos : 0 < alphaNumerator
  alphaDenominator_pos : 0 < alphaDenominator
  nuDenominator_pos : 0 < nuDenominator
  admissible : alphaNumerator * nuDenominator <
    alphaDenominator * (nuNumerator + nuDenominator)

def marked (D : Parameters) : ℕ := D.alphaNumerator * D.nuDenominator

def total (D : Parameters) : ℕ := D.alphaDenominator * (D.nuNumerator + D.nuDenominator)

def unmarked (D : Parameters) : ℕ := total D - marked D

def reinforcement (D : Parameters) : ℕ := D.alphaDenominator * D.nuDenominator

theorem marked_pos (D : Parameters) : 0 < marked D :=
  Nat.mul_pos D.alphaNumerator_pos D.nuDenominator_pos

theorem total_eq (D : Parameters) : marked D + unmarked D = total D :=
  Nat.add_sub_of_le D.admissible.le

theorem denominator_eq (D : Parameters) (n : ℕ) :
    D.alphaDenominator * (D.nuNumerator + (n + 1) * D.nuDenominator) =
      marked D + (unmarked D + n * reinforcement D) := by
  rw [← Nat.add_assoc, total_eq]
  unfold total reinforcement
  ring

/-- The continuation probability after `n` source failures. -/
abbrev continuation (D : Parameters) :=
  UrnWaiting.continuation (marked D) (unmarked D) (reinforcement D)

/-- One plus the reciprocal-hazard first-marked waiting count. -/
def law (D : Parameters) : Measure ℕ :=
  (InverseUrn.law 1 (marked D) (unmarked D) (reinforcement D) (marked_pos D)).map Nat.succ

instance (D : Parameters) : IsProbabilityMeasure (law D) := by
  dsimp [law]
  infer_instance

/-- The generalized Sibuya rising-product mass on positive integers. -/
theorem mass (D : Parameters) (n : ℕ) :
    law D {n + 1} = InverseUrn.positiveMass 0 (marked D) (unmarked D)
      (reinforcement D) n := by
  rw [law, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hpre : Nat.succ ⁻¹' ({n + 1} : Set ℕ) = {n} := by ext; simp
  rw [hpre, InverseUrn.mass_positive]

end

end SampLib.GeneralizedSibuya
