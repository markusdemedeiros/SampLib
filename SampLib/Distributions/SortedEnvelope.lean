import SampLib.Distributions.SortedWeights
import SampLib.Distributions.GroupedEnvelopeCoin

/-! # The labelled categorical law of sorted dyadic rejection -/

open MeasureTheory
open scoped ENNReal NNReal

namespace SampLib.SortedChoice

noncomputable section

abbrev envelopes (ws : List ℕ) (asc : Bool) : List ℕ :=
  GroupedEnvelope.masses ws.length (SortedWeights.envelope ws asc)

abbrev envelopeTotal (ws : List ℕ) (asc : Bool) : ℕ :=
  GroupedEnvelope.total ws.length (SortedWeights.envelope ws asc)

private theorem dominates (ws : List ℕ) (asc : Bool)
    (hs : ws.Pairwise (SortedWeights.Ordered asc)) :
    GroupedEnvelope.Dominates ws.length (SortedWeights.value ws asc)
      (SortedWeights.envelope ws asc) := by
  intro k hk r hr
  exact SortedWeights.envelope_bound ws asc hs k r hk hr

theorem envelopes_pos (ws : List ℕ) (asc : Bool) (ht : 0 < ws.sum)
    (hs : ws.Pairwise (SortedWeights.Ordered asc)) : 0 < (envelopes ws asc).sum := by
  rw [GroupedEnvelope.masses_sum]
  apply GroupedEnvelope.total_pos ws.length (SortedWeights.value ws asc)
    (SortedWeights.envelope ws asc) (dominates ws asc hs)
  change 0 < ∑ i ∈ Finset.range ws.length, SortedWeights.value ws asc i
  rwa [SortedWeights.value_sum]

/-- Each group receives its exact accepted label credit and amplified retry credit. -/
def groupCredit (ws : List ℕ) (asc : Bool) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) : ℕ → ℝ≥0∞ :=
  GroupedEnvelope.groupCredit ws.length (SortedWeights.value ws asc)
    (SortedWeights.envelope ws asc) (fun i => F (SortedWeights.index ws.length asc i))
    ((∫⁻ i, F i ∂WeightedChoice.law ws) + GroupedEnvelope.factor (envelopeTotal ws asc) * ε)

/-- Reversing the traversal preserves labels; the unused integer mass funds termination. -/
theorem expectation_preservation (ws : List ℕ) (asc : Bool) (ht : 0 < ws.sum)
    (hs : ws.Pairwise (SortedWeights.Ordered asc)) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ k, groupCredit ws asc F ε k ∂WeightedChoice.law (envelopes ws asc)) ≤
      (∫⁻ i, F i ∂WeightedChoice.law ws) + ε := by
  have htotal : GroupedEnvelope.weightTotal ws.length (SortedWeights.value ws asc) = ws.sum :=
    SortedWeights.value_sum ws asc
  have h := GroupedEnvelope.expectation_preservation ws.length (SortedWeights.value ws asc)
    (SortedWeights.envelope ws asc) (dominates ws asc hs) (htotal ▸ ht)
    (fun i => F (SortedWeights.index ws.length asc i)) ε
  simpa only [SortedWeights.value_credit, htotal, ← WeightedChoice.lintegral_law,
    groupCredit] using h

end

end SampLib.SortedChoice
