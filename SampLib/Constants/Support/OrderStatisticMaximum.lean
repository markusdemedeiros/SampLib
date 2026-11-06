import SampLib.Continuous.OrderStatistic
import SampLib.Constants.Laws.MaximumUniform

/-! # The maximum uniform order statistic

The last sorted entry is the recursive maximum. This identifies a measurable
scalar proposal without requiring measurable encodings of arbitrary sorted lists.
-/

open Set ProbLang MeasureTheory
open LawfulProbLangℝ (unifUnit)
open scoped ENNReal

namespace SampLib.OrderStatisticMaximum

noncomputable section

open OrderStatistic (Sample samples selected)

def maximum : (n : ℕ) → Sample (n + 1) → ℝ
  | 0, s => s.1
  | n + 1, s => max s.1 (maximum n s.2)

@[fun_prop] theorem measurable_maximum (n : ℕ) : Measurable (maximum n) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih => exact measurable_fst.max (ih.comp measurable_snd)

private theorem maximum_mem (n : ℕ) (s : Sample (n + 1)) :
    maximum n s ∈ samples (n + 1) s := by
  induction n with
  | zero => simp [maximum, samples]
  | succ n ih =>
    rcases le_total s.1 (maximum n s.2) with h | h
    · simpa only [maximum, max_eq_right h, samples, List.mem_cons] using
        Or.inr (ih s.2)
    · simp only [maximum, max_eq_left h, samples, List.mem_cons, true_or]

private theorem le_maximum (n : ℕ) (s : Sample (n + 1)) :
    ∀ a ∈ samples (n + 1) s, a ≤ maximum n s := by
  induction n with
  | zero => simp [maximum, samples]
  | succ n ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_max_left _ _
    · exact (ih s.2 a ha).trans (le_max_right _ _)

/-- Sorting and selecting its final entry computes the same maximum, including ties. -/
theorem selected_eq_maximum (n : ℕ) (s : Sample (n + 1)) :
    selected (n + 1) (n + 1) ⟨by omega, le_rfl⟩ s = maximum n s := by
  let sorted := OrderStatistic.sorted (n + 1) s
  have hne : sorted ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp [sorted]
  have hlast : sorted.getLast hne = selected (n + 1) (n + 1) ⟨by omega, le_rfl⟩ s := by
    simp only [List.getLast_eq_getElem, sorted, selected, List.get_eq_getElem,
      OrderStatistic.sorted_length, Nat.add_sub_cancel_right]
  have hmem : selected (n + 1) (n + 1) ⟨by omega, le_rfl⟩ s ∈ samples (n + 1) s := by
    apply (OrderStatistic.sorted_perm (n + 1) s).mem_iff.mp
    unfold selected
    exact List.get_mem _ _
  apply le_antisymm (le_maximum n s _ hmem)
  have hmax := maximum_mem n s
  have hsorted := (OrderStatistic.sorted_perm (n + 1) s).mem_iff.mpr hmax
  rw [← hlast]
  exact (OrderStatistic.sorted_ordered (n + 1) s).rel_getLast hsorted

/-- The scalar law of the maximum of `n+1` independent unit uniforms. -/
def law (n : ℕ) : Measure ℝ := (OrderStatistic.law (n + 1)).map (maximum n)

instance (n : ℕ) : IsProbabilityMeasure (law n) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_maximum n) MeasurableSet.univ]
    exact (OrderStatistic.instIsProbabilityMeasureSampleLaw (n + 1)).measure_univ

/-- All coordinates must lie below the threshold, so their CDF probabilities multiply. -/
theorem law_apply_Iic (n : ℕ) (t : ℝ) : law n (Iic t) = (unifUnit (Iic t)) ^ (n + 1) := by
  induction n with
  | zero =>
    change ((unifUnit.prod (Measure.dirac ())).map Prod.fst) (Iic t) = _
    rw [Measure.map_apply measurable_fst measurableSet_Iic,
      show Prod.fst ⁻¹' Iic t = Iic t ×ˢ (univ : Set Unit) by
        ext s
        simp, Measure.prod_prod]
    simp
  | succ n ih =>
    have := OrderStatistic.instIsProbabilityMeasureSampleLaw (n + 1)
    have hprevious : OrderStatistic.law (n + 1) ((maximum n) ⁻¹' Iic t) =
        (unifUnit (Iic t)) ^ (n + 1) := by
      rw [← Measure.map_apply (measurable_maximum n) measurableSet_Iic]
      exact ih
    have hset : (fun s : ℝ × Sample (n + 1) => max s.1 (maximum n s.2)) ⁻¹' Iic t =
        Iic t ×ˢ ((maximum n) ⁻¹' Iic t) := by
      ext s
      change max s.1 (maximum n s.2) ≤ t ↔ s.1 ≤ t ∧ maximum n s.2 ≤ t
      exact max_le_iff
    change ((unifUnit.prod (OrderStatistic.law (n + 1))).map
      (fun s : ℝ × Sample (n + 1) => max s.1 (maximum n s.2))) (Iic t) = _
    have hf : Measurable (fun s : ℝ × Sample (n + 1) => max s.1 (maximum n s.2)) := by
      fun_prop
    rw [Measure.map_apply hf measurableSet_Iic,
      hset, Measure.prod_prod, hprevious]
    exact (mul_comm _ _).trans (pow_succ _ (n + 1)).symm

/-- Equality of CDFs identifies the classical power density. -/
theorem law_eq_density (n : ℕ) : law n = MaximumUniform.law n := by
  apply Measure.ext_of_Iic
  intro t
  rw [law_apply_Iic, MaximumUniform.law_apply_Iic]

theorem expectation (n : ℕ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ s, F (maximum n s) ∂OrderStatistic.law (n + 1) =
      ∫⁻ t, F t ∂MaximumUniform.law n := by
  rw [← law_eq_density, law, lintegral_map hF (measurable_maximum n)]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

/-- The actual sorting sampler realizes density `(n+1)t^n`, for every positive sample size. -/
theorem orderStatistic_max_distSpec (E : CoPset) (n : ℕ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.orderStatistic #int ((n + 1 : ℕ) : ℤ) #int ((n + 1 : ℕ) : ℤ))
      (MaximumUniform.law n) Val.real where
  spec F hF := by
    have := OrderStatistic.instIsProbabilityMeasureSampleLaw (n + 1)
    iintro Hcredit
    isimp only [← expectation n F hF] at Hcredit
    iapply ((OrderStatistic.orderStatistic_distSpec E (n + 1) (n + 1)
      ⟨by omega, le_rfl⟩).wp (fun s => F (maximum n s))
      (hF.comp (measurable_maximum n)) _) $$ Hcredit
    iintro %s Hcredit
    iexists maximum n s
    iframe Hcredit
    ipureintro
    rw [selected_eq_maximum]

end specification

end

end SampLib.OrderStatisticMaximum
