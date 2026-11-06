import SampLib.Samplers.SampleWithReplacement

/-! # Independent finite lists

A chronological list of iid draws, with the vector-to-list bridge used by
`repeatSample`. Splitting an independent block exposes its prefix and suffix.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.IIDList

noncomputable section

variable {α : Type _} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

/-- Independent draws in chronological order. -/
def law (μ : Measure α) : ℕ → Measure (List α)
  | 0 => Measure.dirac []
  | n + 1 => (μ.prod (law μ n)).map (fun z => z.1 :: z.2)

instance (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (law μ n) := by
  induction n with
  | zero => dsimp [law]; infer_instance
  | succ n IH =>
    let := IH
    constructor
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

omit [Countable α] in
@[simp] theorem expectation_zero (μ : Measure α) (F : List α → ℝ≥0∞) :
    ∫⁻ xs, F xs ∂law μ 0 = F [] := by simp [law]

/-- Condition on the first independent draw. -/
theorem expectation (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ)
    (F : List α → ℝ≥0∞) :
    ∫⁻ x, (∫⁻ xs, F (x :: xs) ∂law μ n) ∂μ = ∫⁻ xs, F xs ∂law μ (n + 1) := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]

/-- The existing vector law and chronological list law give the same expectations. -/
theorem vector_expectation (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ)
    (F : List α → ℝ≥0∞) :
    ∫⁻ v, F (List.ofFn v) ∂SampleWithReplacement.law μ n = ∫⁻ xs, F xs ∂law μ n := by
  induction n generalizing F with
  | zero => simp [SampleWithReplacement.law, law]
  | succ n IH =>
    rw [SampleWithReplacement.lintegral_law_succ μ n _ (measurable_of_countable _),
      ← expectation]
    simp only [List.ofFn_succ]
    apply lintegral_congr_ae
    exact Filter.Eventually.of_forall fun x => IH (fun xs => F (x :: xs))

theorem vector_map (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) :
    (SampleWithReplacement.law μ n).map List.ofFn = law μ n := by
  apply Measure.ext_of_lintegral
  intro F _
  rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    vector_expectation]

theorem length_ae (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) :
    ∀ᵐ xs ∂law μ n, xs.length = n := by
  induction n with
  | zero => simp [law]
  | succ n IH =>
    rw [law, ae_map_iff (measurable_of_countable _).aemeasurable
      (Set.to_countable _).measurableSet]
    apply (Measure.ae_prod_iff_ae_ae (Set.to_countable _).measurableSet).2
    exact Filter.Eventually.of_forall fun x => IH.mono fun xs hxs => by simp [hxs]

/-- Independent prefix and suffix blocks concatenate to the full iid block. -/
theorem append_expectation (μ : Measure α) [IsProbabilityMeasure μ] (m n : ℕ)
    (F : List α → ℝ≥0∞) :
    ∫⁻ xs, (∫⁻ ys, F (xs ++ ys) ∂law μ n) ∂law μ m = ∫⁻ zs, F zs ∂law μ (m + n) := by
  induction m generalizing F with
  | zero => simp [law]
  | succ m IH =>
    rw [Nat.succ_add, ← expectation, ← expectation]
    simp only [List.cons_append]
    apply lintegral_congr_ae
    exact Filter.Eventually.of_forall fun x => IH (fun xs => F (x :: xs))

/-- Taking the first `m` entries of a longer iid list retains the `m`-draw law. -/
theorem take_map (μ : Measure α) [IsProbabilityMeasure μ] (m n : ℕ) (hmn : m ≤ n) :
    (law μ n).map (List.take m) = law μ m := by
  have hn : n = m + (n - m) := (Nat.add_sub_of_le hmn).symm
  rw [hn]
  apply Measure.ext_of_lintegral
  intro F _
  rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    ← append_expectation]
  apply lintegral_congr_ae
  filter_upwards [length_ae μ m] with xs hxs
  simp [← hxs]

end

end SampLib.IIDList
