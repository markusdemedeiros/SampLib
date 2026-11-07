module

public import SampLib.Combinatorial.Laws.CompositionCuts
public import SampLib.Combinatorial.Laws.SampleInOrder
public import Mathlib.Probability.Distributions.Uniform

@[expose] public section

/-! # Uniform compositions from interior cuts

Uniform interior cuts give uniform positive compositions through their gaps.
Subtracting one from every part gives the corresponding weak composition.
-/

open MeasureTheory Measure
open scoped ENNReal Classical

namespace SampLib.Compositions

noncomputable section

local instance : MeasurableSpace (List ℤ) := ⊤

theorem cut_count_le (n total : ℕ) (h : n ≤ total) :
    n - 1 ≤ (IntegerRange.interval 1 (total - 1)).length := by
  rw [interval_length]
  omega

/-- Choose the interior cuts uniformly and take their consecutive gaps. -/
def law (n total : ℕ) (_hn : 0 < n) (ht : n ≤ total) : Measure (List ℤ) :=
  (SampleInOrder.law (IntegerRange.interval 1 (total - 1)) (n - 1)
    (cut_count_le n total ht)).map (gaps total 0)

instance (n total : ℕ) (hn : 0 < n) (ht : n ≤ total) :
    IsProbabilityMeasure (law n total hn ht) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- The cut-to-gap bijection transports every continuation expectation. -/
theorem expectation (n total : ℕ) (hn : 0 < n) (ht : n ≤ total)
    (F : List ℤ → ℝ≥0∞) :
    ∫⁻ cuts, F (gaps total 0 cuts) ∂SampleInOrder.law
      (IntegerRange.interval 1 (total - 1)) (n - 1) (cut_count_le n total ht) =
      ∫⁻ parts, F parts ∂law n total hn ht := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

private theorem sum_dirac_preimage (xs : List (List ℤ)) (f : List ℤ → List ℤ)
    (parts : List ℤ) :
    ((xs.map (dirac : List ℤ → Measure (List ℤ))).sum) (f ⁻¹' {parts}) =
      ((xs.map f).count parts : ℝ≥0∞) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases h : f x = parts <;>
      simp [Set.indicator, h, ih, add_comm]

/-- Every positive composition has reciprocal binomial-coefficient mass. -/
theorem law_singleton (n total : ℕ) (hn : 0 < n) (ht : n ≤ total) (parts : List ℤ) :
    law n total hn ht {parts} =
      if positive n total parts then ((total - 1).choose (n - 1) : ℝ≥0∞)⁻¹ else 0 := by
  rw [law, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  simp only [SampleInOrder.law, Measure.smul_apply, smul_eq_mul, sum_dirac_preimage]
  change ((IntegerRange.interval 1 (total - 1)).length.choose (n - 1) : ℝ≥0∞)⁻¹ *
    ((enumeration n total).count parts : ℝ≥0∞) = _
  rw [interval_length]
  by_cases hp : positive n total parts
  · rw [ite_eq_left hp, List.count_eq_one_of_mem (enumeration_nodup n total)
      ((mem_enumeration n total hn ht parts).mpr hp)]
    simp
  · rw [ite_eq_right hp, List.count_eq_zero_of_not_mem
      (fun h => hp ((mem_enumeration n total hn ht parts).mp h))]
    simp

/-- The cut-gap enumeration realizes the usual uniform finite-set law. -/
theorem law_eq_uniform (n total : ℕ) (hn : 0 < n) (ht : n ≤ total) :
    law n total hn ht = uniformOfFinset (enumeration n total).toFinset := by
  apply Measure.ext_of_singleton
  intro parts
  rw [law_singleton, uniformOfFinset_apply_singleton]
  simp only [List.mem_toFinset, mem_enumeration n total hn ht,
    List.toFinset_card_of_nodup (enumeration_nodup n total), enumeration_length]

/-- Weak compositions have nonnegative ordered parts of the prescribed total. -/
def weak (n total : ℕ) (parts : List ℤ) : Prop :=
  parts.length = n ∧ (∀ x ∈ parts, 0 ≤ x) ∧ parts.sum = (total : ℤ)

def addOne (parts : List ℤ) : List ℤ := parts.map (· + 1)

def subtractOne (parts : List ℤ) : List ℤ := parts.map (· - 1)

@[simp] theorem addOne_subtractOne (parts : List ℤ) : addOne (subtractOne parts) = parts := by
  simp [addOne, subtractOne, List.map_map, Function.comp_def]

@[simp] theorem subtractOne_addOne (parts : List ℤ) : subtractOne (addOne parts) = parts := by
  simp [addOne, subtractOne, List.map_map, Function.comp_def]

theorem sum_addOne (parts : List ℤ) : (addOne parts).sum = parts.sum + parts.length := by
  simp [addOne, List.sum_map_add]

/-- Adding one to every part is the stars-and-bars bijection. -/
theorem positive_addOne_iff (n total : ℕ) (parts : List ℤ) :
    positive n (total + n) (addOne parts) ↔ weak n total parts := by
  unfold positive weak
  rw [show (addOne parts).length = parts.length by simp [addOne], sum_addOne]
  constructor
  · rintro ⟨hl, hp, hs⟩
    refine ⟨hl, ?_, ?_⟩
    · intro x hx
      have := hp (x + 1) (List.mem_map.mpr ⟨x, hx, rfl⟩)
      omega
    · push_cast at hs
      omega
  · rintro ⟨hl, hp, hs⟩
    refine ⟨hl, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have := hp y hy
      omega
    · push_cast
      omega

/-- Uniform weak compositions, obtained by subtracting one from every positive part. -/
def weakLaw (n total : ℕ) (hn : 0 < n) : Measure (List ℤ) :=
  (law n (total + n) hn (by omega)).map subtractOne

instance (n total : ℕ) (hn : 0 < n) : IsProbabilityMeasure (weakLaw n total hn) where
  measure_univ := by
    rw [weakLaw, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

theorem weak_expectation (n total : ℕ) (hn : 0 < n) (F : List ℤ → ℝ≥0∞) :
    ∫⁻ parts, F (subtractOne parts) ∂law n (total + n) hn (by omega) =
      ∫⁻ parts, F parts ∂weakLaw n total hn := by
  rw [weakLaw, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

/-- Every weak composition has the same stars-and-bars probability. -/
theorem weakLaw_singleton (n total : ℕ) (hn : 0 < n) (parts : List ℤ) :
    weakLaw n total hn {parts} =
      if weak n total parts then ((total + n - 1).choose (n - 1) : ℝ≥0∞)⁻¹ else 0 := by
  have hpre : subtractOne ⁻¹' {parts} = {addOne parts} := by
    ext xs
    change subtractOne xs = parts ↔ xs = addOne parts
    constructor
    · intro h
      simpa using congrArg addOne h
    · rintro rfl
      simp
  rw [weakLaw, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    hpre, law_singleton, positive_addOne_iff]

end

end SampLib.Compositions
