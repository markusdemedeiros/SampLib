import SampLib.Discrete.Laws.WeightedChoice
import SampLib.Common.Laws.WeightedSupport
import SampLib.Common.Laws.WeightedPositiveSupport

/-! # Wallenius draw weights

Each color has weight its remaining count times its odds. A valid request
leaves positive total weight, and the weighted choice selects a present color.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.Wallenius

noncomputable section

abbrev weights (pop odds : List ℕ) : List ℕ := List.zipWith (· * ·) pop odds

abbrev decrement (pop : List ℕ) (i : ℕ) : List ℕ := pop.modify i (· - 1)

abbrev increment (counts : List ℕ) (i : ℕ) : List ℕ := counts.modify i (· + 1)

theorem weights_getD (pop odds : List ℕ) (i : ℕ) :
    (weights pop odds)[i]?.getD 0 = pop[i]?.getD 0 * odds[i]?.getD 0 := by
  induction pop generalizing odds i with
  | nil => simp [weights]
  | cons c pop IH =>
    cases odds with
    | nil => simp [weights]
    | cons o odds =>
      cases i with
      | zero => simp [weights]
      | succ i => simpa [weights] using IH odds i

theorem weights_length (pop odds : List ℕ) (hlen : pop.length = odds.length) :
    (weights pop odds).length = pop.length := by simp [weights, hlen]

theorem request_weight_pos (pop odds : List ℕ) (n : ℕ) (hn : n + 1 ≤ pop.sum)
    (hlen : pop.length = odds.length) (hodds : ∀ o ∈ odds, 0 < o) :
    0 < (weights pop odds).sum := by
  induction pop generalizing odds with
  | nil => simp at hn
  | cons c pop IH =>
    cases odds with
    | nil => simp at hlen
    | cons o odds =>
      have ho := hodds o (by simp)
      by_cases hc : 0 < c
      · have hp := Nat.mul_pos hc ho
        simp only [weights, List.zipWith_cons_cons, List.sum_cons]
        omega
      · have hc0 := Nat.eq_zero_of_not_pos hc
        have htail := IH odds (by simpa [hc0] using hn) (by simpa using hlen)
          (fun x hx => hodds x (by simp [hx]))
        simpa [weights, hc0] using htail

theorem decrement_sum (pop : List ℕ) (i : ℕ) (hi : 0 < pop[i]?.getD 0) :
    (decrement pop i).sum + 1 = pop.sum := by
  induction pop generalizing i with
  | nil => simp at hi
  | cons c pop IH =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.getD_some] at hi
      simp only [decrement, List.modify_zero_cons, List.sum_cons]
      omega
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      have := IH i hi
      simp only [decrement] at this
      simp only [decrement, List.modify_succ_cons, List.sum_cons]
      omega

theorem remaining_request (pop : List ℕ) (i n : ℕ) (hi : 0 < pop[i]?.getD 0)
    (hn : n + 1 ≤ pop.sum) : n ≤ (decrement pop i).sum := by
  have := decrement_sum pop i hi
  omega

/-- Every selected color exists and still has a ball; zero-mass colors need no credit. -/
theorem selected (pop odds : List ℕ) (hlen : pop.length = odds.length) :
    ∀ᵐ i ∂WeightedChoice.law (weights pop odds), i < pop.length ∧ 0 < pop[i]?.getD 0 := by
  apply ((WeightedChoice.ae_lt_length (weights pop odds)).and
    (WeightedChoice.ae_pos_weight (weights pop odds))).mono
  intro i hi
  refine ⟨by simpa [weights_length pop odds hlen] using hi.1, ?_⟩
  by_contra h
  have hz := Nat.eq_zero_of_not_pos h
  have hp := hi.2
  simp [weights_getD, hz] at hp

end

end SampLib.Wallenius
