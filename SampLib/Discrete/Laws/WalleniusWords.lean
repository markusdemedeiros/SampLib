import Metrology.ProbLang.Discrete
import SampLib.Discrete.Laws.WalleniusWeights

/-! # Wallenius color words

Each word has the product of its successive remaining-count times odds ratios.
With equal odds, this is the ordinary without-replacement likelihood.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.Wallenius

noncomputable section

/-- A normalized extension stops at exhaustion; valid requests always have their full length. -/
def wordLaw (pop odds : List ℕ) : ℕ → Measure (List ℕ)
  | 0 => Measure.dirac []
  | n + 1 => if (weights pop odds).sum = 0 then Measure.dirac [] else
      (WeightedChoice.law (weights pop odds)).bind
        (fun i => (wordLaw (decrement pop i) odds n).map (List.cons i))

instance (pop odds : List ℕ) (n : ℕ) : IsProbabilityMeasure (wordLaw pop odds n) := by
  induction n generalizing pop with
  | zero => dsimp [wordLaw]; infer_instance
  | succ n IH =>
    by_cases hs : (weights pop odds).sum = 0
    · simp only [wordLaw, ite_eq_left hs]
      infer_instance
    · let : NeZero (weights pop odds).sum := ⟨hs⟩
      let (i : ℕ) := IH (decrement pop i)
      simp only [wordLaw, ite_eq_right hs]
      constructor
      rw [Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
      have hm (i : ℕ) : (wordLaw (decrement pop i) odds n).map (List.cons i) Set.univ = 1 := by
        rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
        simp
      simp_rw [hm]
      simp

/-- One physical ball of the selected color is removed at each prefix. -/
def remaining (pop : List ℕ) (history : List ℕ) : List ℕ := history.foldl decrement pop

/-- The current color probability is its remaining ball count times its fixed odds. -/
def ratio (pop odds : List ℕ) (i : ℕ) : ℝ≥0∞ :=
  ((pop[i]?.getD 0 * odds[i]?.getD 0 : ℕ) : ℝ≥0∞) / (weights pop odds).sum

/-- The successive ratio product, before collecting color counts. -/
def likelihood (pop odds : List ℕ) : List ℕ → ℝ≥0∞
  | [] => 1
  | i :: is => ratio pop odds i * likelihood (decrement pop i) odds is

/-- The likelihood is explicitly a product over prefixes of the color word. -/
theorem likelihood_product (pop odds word : List ℕ) :
    likelihood pop odds word = ∏ k ∈ Finset.range word.length,
      ratio (remaining pop (word.take k)) odds (word[k]?.getD 0) := by
  induction word generalizing pop with
  | nil => simp [likelihood]
  | cons i is IH =>
    rw [List.length_cons, Finset.prod_range_succ']
    simp only [List.take_zero, remaining, List.foldl_nil, List.getElem?_cons_zero,
      Option.getD_some, List.take_succ_cons, List.foldl_cons, List.getElem?_cons_succ]
    rw [likelihood, IH]
    exact mul_comm _ _

private theorem singleton_cons (pop odds : List ℕ) (hs : 0 < (weights pop odds).sum)
    (n i : ℕ) (is : List ℕ) :
    wordLaw pop odds (n + 1) {i :: is} =
      ratio pop odds i * wordLaw (decrement pop i) odds n {is} := by
  rw [wordLaw, ite_eq_right hs.ne', Measure.bind_apply (measurableSet_singleton _)
    (measurable_of_countable _).aemeasurable]
  have hkernel (j : ℕ) : (wordLaw (decrement pop j) odds n).map (List.cons j) {i :: is} =
      ({i} : Set ℕ).indicator (fun _ => wordLaw (decrement pop i) odds n {is}) j := by
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    have hpre : List.cons j ⁻¹' ({i :: is} : Set (List ℕ)) =
        if j = i then {is} else ∅ := by
      ext xs
      by_cases h : j = i <;> simp [h]
    rw [hpre]
    by_cases h : j = i <;> simp [h]
  simp_rw [hkernel]
  rw [lintegral_indicator_const (measurableSet_singleton _), WeightedChoice.law_singleton,
    weights_getD]
  exact mul_comm _ _

private theorem weight_le_sum (ws : List ℕ) (i : ℕ) : ws[i]?.getD 0 ≤ ws.sum := by
  induction ws generalizing i with
  | nil => simp
  | cons w ws IH =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.getElem?_cons_succ, List.sum_cons]
      exact (IH i).trans (Nat.le_add_left _ _)

/-- Full-length singleton masses are the canonical successive color-word likelihoods. -/
theorem word_likelihood (pop odds word : List ℕ) :
    wordLaw pop odds word.length {word} = likelihood pop odds word := by
  induction word generalizing pop with
  | nil => simp [wordLaw, likelihood]
  | cons i is IH =>
    by_cases hs : (weights pop odds).sum = 0
    · have hw : pop[i]?.getD 0 * odds[i]?.getD 0 = 0 := by
        have := weight_le_sum (weights pop odds) i
        rw [weights_getD, hs] at this
        omega
      simp [wordLaw, hs, likelihood, ratio, hw]
    · rw [List.length_cons, singleton_cons pop odds (Nat.pos_of_ne_zero hs), IH]
      rfl

/-- Removing one ball changes only its color's remaining count. -/
theorem decrement_getD (pop : List ℕ) (i j : ℕ) :
    (decrement pop i)[j]?.getD 0 =
      if i = j then pop[j]?.getD 0 - 1 else pop[j]?.getD 0 := by
  rw [List.getElem?_modify]
  cases pop[j]? <;> by_cases hij : i = j <;> simp [hij]

/-- Remaining counts are initial counts minus occurrences in the observed prefix. -/
theorem remaining_getD (pop history : List ℕ) (j : ℕ) :
    (remaining pop history)[j]?.getD 0 = pop[j]?.getD 0 - history.count j := by
  induction history generalizing pop with
  | nil => simp [remaining]
  | cons i is IH =>
    change (remaining (decrement pop i) is)[j]?.getD 0 = _
    rw [IH, decrement_getD]
    by_cases h : i = j <;> simp [h, Nat.sub_sub, Nat.add_comm]

private theorem singleton_nil (pop odds : List ℕ) (hs : 0 < (weights pop odds).sum)
    (n : ℕ) : wordLaw pop odds (n + 1) {[]} = 0 := by
  rw [wordLaw, ite_eq_right hs.ne', Measure.bind_apply (measurableSet_singleton _)
    (measurable_of_countable _).aemeasurable]
  have hpre (i : ℕ) : List.cons i ⁻¹' ({[]} : Set (List ℕ)) = ∅ := by ext is; simp
  simp [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _), hpre]

private theorem support_of_mass (pop odds : List ℕ) (n : ℕ) (hn : n ≤ pop.sum)
    (hlen : pop.length = odds.length) (hodds : ∀ o ∈ odds, 0 < o)
    (word : List ℕ) (hmass : wordLaw pop odds n {word} ≠ 0) :
    word.length = n ∧ ∀ i, word.count i ≤ pop[i]?.getD 0 := by
  induction n generalizing pop word with
  | zero =>
    have he : word = [] := by
      by_contra h
      apply hmass
      simp [wordLaw, h]
    subst word
    simp
  | succ n IH =>
    have hs := request_weight_pos pop odds n hn hlen hodds
    cases word with
    | nil => exact (hmass (singleton_nil pop odds hs n)).elim
    | cons i is =>
      rw [singleton_cons pop odds hs n i is] at hmass
      have hi : 0 < pop[i]?.getD 0 := by
        by_contra h
        apply (mul_ne_zero_iff.mp hmass).1
        simp [ratio, Nat.eq_zero_of_not_pos h]
      have htail := IH (pop := decrement pop i) (word := is)
        (remaining_request pop i n hi hn) (by simpa [decrement] using hlen)
        (mul_ne_zero_iff.mp hmass).2
      refine ⟨by simp [htail.1], ?_⟩
      intro j
      have hj := htail.2 j
      rw [decrement_getD] at hj
      by_cases hij : i = j
      · subst j
        simp only [ite_true] at hj
        simp only [List.count_cons_self]
        omega
      · simpa [List.count_cons, hij] using hj

/-- Valid urn requests produce their full word length and never overdraw a color. -/
theorem word_support (pop odds : List ℕ) (n : ℕ) (hn : n ≤ pop.sum)
    (hlen : pop.length = odds.length) (hodds : ∀ o ∈ odds, 0 < o) :
    ∀ᵐ word ∂wordLaw pop odds n, word.length = n ∧ ∀ i, word.count i ≤ pop[i]?.getD 0 := by
  apply ae_iff_of_countable.mpr
  exact fun word hm => support_of_mass pop odds n hn hlen hodds word hm

/-- The normalized finite word PMF, with zero mass off the requested length. -/
theorem wordLaw_singleton (pop odds : List ℕ) (n : ℕ) (hn : n ≤ pop.sum)
    (hlen : pop.length = odds.length) (hodds : ∀ o ∈ odds, 0 < o) (word : List ℕ) :
    wordLaw pop odds n {word} = if word.length = n then likelihood pop odds word else 0 := by
  by_cases h : word.length = n
  · rw [ite_eq_left h, ← h, word_likelihood]
  · rw [ite_eq_right h]
    by_contra hm
    exact h ((ae_iff_of_countable.mp (word_support pop odds n hn hlen hodds)) word hm).1

@[simp] theorem remaining_length (pop history : List ℕ) :
    (remaining pop history).length = pop.length := by
  induction history generalizing pop with
  | nil => rfl
  | cons i is IH =>
    change (remaining (decrement pop i) is).length = _
    rw [IH]
    simp [decrement]

@[simp] theorem weights_unit (pop : List ℕ) : weights pop (List.replicate pop.length 1) = pop := by
  induction pop with
  | nil => rfl
  | cons c pop IH => simpa [weights, List.replicate_succ] using congrArg (List.cons c) IH

/-- Equal odds reduce the color probability to its remaining population proportion. -/
theorem ratio_unit (pop : List ℕ) (i : ℕ) :
    ratio pop (List.replicate pop.length 1) i = (pop[i]?.getD 0 : ℝ≥0∞) / pop.sum := by
  rw [ratio, ← weights_getD, weights_unit]

/-- The equal-odds law is the ordinary without-replacement color-word likelihood. -/
theorem equal_odds_likelihood (pop word : List ℕ) :
    likelihood pop (List.replicate pop.length 1) word =
      ∏ k ∈ Finset.range word.length,
        ((remaining pop (word.take k))[word[k]?.getD 0]?.getD 0 : ℝ≥0∞) /
          (remaining pop (word.take k)).sum := by
  rw [likelihood_product]
  apply Finset.prod_congr rfl
  intro k hk
  rw [← remaining_length pop (word.take k)]
  exact ratio_unit _ _

end

end SampLib.Wallenius
