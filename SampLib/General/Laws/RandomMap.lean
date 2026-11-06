import SampLib.General.Laws.Markov

/-! # Random transition map law

Each row independently chooses one destination, so one sampled map can move several states
with the same randomness.
-/

open MeasureTheory Measure
open scoped ENNReal

namespace SampLib.RandomMap

noncomputable section

abbrev Row := MarkovChain.Row

/-- Independent categorical draws, one for each transition row. -/
def law : List Row → Measure (List ℕ)
  | [] => dirac []
  | r :: rs => ((law rs).prod (WeightedChoice.law r.val)).map (fun z => z.2 :: z.1)

instance (rows : List Row) : IsProbabilityMeasure (law rows) := by
  induction rows with
  | nil => dsimp [law]; infer_instance
  | cons r rs ih =>
    let : NeZero r.val.sum := ⟨r.property.ne'⟩
    constructor
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Independent rows factor the map expectation into successive expectations. -/
theorem expectation (r : Row) (rs : List Row) (F : List ℕ → ℝ≥0∞) :
    ∫⁻ ys, (∫⁻ j, F (j :: ys) ∂WeightedChoice.law r.val) ∂law rs =
      ∫⁻ ys, F ys ∂law (r :: rs) := by
  let : NeZero r.val.sum := ⟨r.property.ne'⟩
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]

end

end SampLib.RandomMap
