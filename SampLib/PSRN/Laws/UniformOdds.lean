module

public import SampLib.Common.Laws.DyadicPosterior
public import SampLib.PSRN.Laws.ReciprocalUniform
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! # The odds of a unit uniform

The threshold `u/(1-u) ≤ t` cuts off the initial interval of length `t/(1+t)`.
Thus uniform odds have the scale-one Pareto law translated by minus one.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SampLib.UniformOdds

noncomputable section

def transform (u : ℝ) : ℝ := u / (1 - u)

theorem measurable_transform : Measurable transform :=
  measurable_id.div (measurable_const.sub measurable_id)

def law : Measure ℝ := DyadicPosterior.unitLaw.map transform

instance : IsProbabilityMeasure law := by unfold law; infer_instance

theorem expectation (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x ∂law) = ∫⁻ u, F (transform u) ∂DyadicPosterior.unitLaw :=
  lintegral_map hF measurable_transform

private theorem threshold {u t : ℝ} (hu : u ∈ Ico 0 1) (ht : 0 ≤ t) :
    transform u ≤ t ↔ u ≤ t / (1 + t) := by
  rw [transform, div_le_iff₀ (by linarith [hu.2] : 0 < 1 - u),
    le_div_iff₀ (by linarith : 0 < 1 + t)]
  constructor <;> intro h <;> nlinarith

/-- The odds distribution function, including its zero endpoint. -/
theorem law_Iic (t : ℝ) : law (Iic t) = ENNReal.ofReal (if 0 ≤ t then t / (1 + t) else 0) := by
  rw [law, Measure.map_apply measurable_transform measurableSet_Iic,
    DyadicPosterior.unitLaw, Measure.restrict_apply (measurableSet_Iic.preimage measurable_transform)]
  by_cases ht : 0 ≤ t
  · rw [ite_eq_left ht]
    have hden : 0 < 1 + t := by linarith
    have hq : t / (1 + t) < 1 := (div_lt_one hden).mpr (by linarith)
    have heq : (transform ⁻¹' Iic t) ∩ Ico 0 1 = Icc 0 (t / (1 + t)) := by
      ext u
      change (transform u ≤ t ∧ 0 ≤ u ∧ u < 1) ↔ 0 ≤ u ∧ u ≤ t / (1 + t)
      constructor
      · rintro ⟨hu, h0, h1⟩
        exact ⟨h0, (threshold ⟨h0, h1⟩ ht).mp hu⟩
      · rintro ⟨h0, hu⟩
        have h1 := hu.trans_lt hq
        exact ⟨(threshold ⟨h0, h1⟩ ht).mpr hu, h0, h1⟩
    rw [heq, Real.volume_Icc, sub_zero]
  · rw [ite_eq_right ht]
    have heq : (transform ⁻¹' Iic t) ∩ Ico 0 1 = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro u ⟨hu, h0, h1⟩
      exact ht ((div_nonneg h0 (by linarith : 0 ≤ 1 - u)).trans hu)
    rw [heq, measure_empty, ENNReal.ofReal_zero]

/-- A canonical shifted-Pareto identification of the normalized odds law. -/
theorem law_eq_shifted_pareto :
    law = (ProbabilityTheory.paretoMeasure 1 1).map (fun x : ℝ => x - 1) := by
  apply Measure.ext_of_Iic
  intro t
  have hshift : Measurable (fun x : ℝ => x - 1) := measurable_id.sub_const 1
  rw [law_Iic, ← ReciprocalUniform.law_eq_pareto,
    Measure.map_apply hshift measurableSet_Iic]
  have heq : (fun x : ℝ => x - 1) ⁻¹' Iic t = Iic (t + 1) := by
    ext x
    change x - 1 ≤ t ↔ x ≤ t + 1
    constructor <;> intro h <;> linarith
  rw [heq, ReciprocalUniform.law_Iic]
  by_cases ht : 0 ≤ t
  · rw [ite_eq_left ht, ite_eq_left (by linarith : 1 ≤ t + 1)]
    congr 1
    have hden : 1 + t ≠ 0 := by linarith
    field_simp
    ring
  · rw [ite_eq_right ht, ite_eq_right (by linarith : ¬1 ≤ t + 1)]

end

end SampLib.UniformOdds
