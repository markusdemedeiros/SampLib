import SampLib.Samplers.WeightedChoice
import SampLib.Distributions.WeightedSupport
import SampLib.Distributions.WeightedPositiveSupport
import SampLib.Distributions.Urn

/-! # Wallenius sampling as a finite color-word likelihood

Each word has the product of its successive remaining-count times odds ratios.
Mapping the word to its color counts gives the multivariate Wallenius law.
-/

open MeasureTheory
open scoped BigOperators ENNReal

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

/-- Counts are returned in the original color order, including colors not drawn. -/
def colorCounts (m : ℕ) (word : List ℕ) : List ℕ :=
  List.ofFn (fun i : Fin m => word.count i.val)

@[simp] theorem colorCounts_length (m : ℕ) (word : List ℕ) :
    (colorCounts m word).length = m := by simp [colorCounts]

@[simp] theorem colorCounts_nil (m : ℕ) : colorCounts m [] = List.replicate m 0 := by
  apply List.ext_getElem
  · simp [colorCounts]
  · intro i hi hj
    simp [colorCounts]

/-- Prefixing a color increments exactly its corresponding count. -/
theorem colorCounts_cons (m i : ℕ) (word : List ℕ) :
    colorCounts m (i :: word) = increment (colorCounts m word) i := by
  apply List.ext_getElem
  · simp [increment]
  · intro j hj hj'
    simp only [increment, List.getElem_modify, colorCounts, List.getElem_ofFn]
    by_cases h : i = j <;> simp [h]

/-- The multivariate Wallenius law is the color-count pushforward of its word likelihood. -/
def law (n : ℕ) (pop odds : List ℕ) : Measure (List ℕ) :=
  (wordLaw pop odds n).map (colorCounts pop.length)

instance (n : ℕ) (pop odds : List ℕ) : IsProbabilityMeasure (law n pop odds) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

@[simp] theorem law_zero (pop odds : List ℕ) :
    law 0 pop odds = Measure.dirac (List.replicate pop.length 0) := by
  rw [law, wordLaw, Measure.map_dirac' (measurable_of_countable _), colorCounts_nil]

theorem support_length (n : ℕ) (pop odds : List ℕ) :
    ∀ᵐ ys ∂law n pop odds, ys.length = pop.length := by
  rw [law]
  apply (ae_map_iff (measurable_of_countable _).aemeasurable
    (Set.to_countable _).measurableSet).2
  exact Filter.Eventually.of_forall (fun word => colorCounts_length pop.length word)

/-- Accumulated color counts combine with the additional draws pointwise. -/
def credit (n : ℕ) (pop odds acc : List ℕ) (F : List ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ys, F (List.zipWith (· + ·) acc ys) ∂law n pop odds

private theorem credit_word (n : ℕ) (pop odds acc : List ℕ) (F : List ℕ → ℝ≥0∞) :
    credit n pop odds acc F =
      ∫⁻ word, F (List.zipWith (· + ·) acc (colorCounts pop.length word))
        ∂wordLaw pop odds n := by
  rw [credit, law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

theorem add_zeros (xs : List ℕ) : List.zipWith (· + ·) xs (List.replicate xs.length 0) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs IH =>
    simpa only [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, Nat.add_zero]
      using congrArg (List.cons x) IH

@[simp] theorem credit_zero (pop odds acc : List ℕ) (hlen : acc.length = pop.length)
    (F : List ℕ → ℝ≥0∞) : credit 0 pop odds acc F = F acc := by
  rw [credit, law_zero, lintegral_dirac, ← hlen, add_zeros]

private theorem add_increment_swap (xs ys : List ℕ) (i : ℕ) :
    List.zipWith (· + ·) (increment xs i) ys =
      List.zipWith (· + ·) xs (increment ys i) := by
  induction xs generalizing ys i with
  | nil => simp [increment]
  | cons x xs IH =>
    cases ys with
    | nil => simp [increment]
    | cons y ys =>
      cases i with
      | zero =>
        simp only [increment, List.modify_zero_cons, List.zipWith_cons_cons]
        congr 1
        omega
      | succ i => simpa [increment] using congrArg (List.cons (x + y)) (IH ys i)

private theorem collect_cons (m : ℕ) (acc : List ℕ) (i : ℕ) (word : List ℕ) :
    List.zipWith (· + ·) acc (colorCounts m (i :: word)) =
      List.zipWith (· + ·) (increment acc i) (colorCounts m word) := by
  rw [colorCounts_cons, add_increment_swap]

/-- Conditioning on the first remaining-count/odds draw preserves arbitrary output credit. -/
theorem word_expectation (pop odds : List ℕ) (n : ℕ) (hs : 0 < (weights pop odds).sum)
    (F : List ℕ → ℝ≥0∞) :
    ∫⁻ i, ∫⁻ word, F (i :: word) ∂wordLaw (decrement pop i) odds n
      ∂WeightedChoice.law (weights pop odds) = ∫⁻ word, F word ∂wordLaw pop odds (n + 1) := by
  rw [wordLaw, ite_eq_right hs.ne', Measure.lintegral_bind
    (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]
  congr 1
  funext i
  exact (lintegral_map (measurable_of_countable _) (measurable_of_countable _)).symm

/-- The first-color update commutes with the count pushforward and preserves its expectation. -/
theorem expectation (pop odds : List ℕ) (n : ℕ) (hs : 0 < (weights pop odds).sum)
    (acc : List ℕ) (F : List ℕ → ℝ≥0∞) :
    ∫⁻ i, credit n (decrement pop i) odds (increment acc i) F
      ∂WeightedChoice.law (weights pop odds) = credit (n + 1) pop odds acc F := by
  simp_rw [credit_word]
  simp only [decrement, List.length_modify]
  simp_rw [← collect_cons]
  exact word_expectation pop odds n hs
    (fun word => F (List.zipWith (· + ·) acc (colorCounts pop.length word)))

/-- Conservation on the full natural domain of positive-odds urn requests. -/
theorem first_color_expectation (pop odds : List ℕ) (n : ℕ) (hn : n + 1 ≤ pop.sum)
    (hlen : pop.length = odds.length) (hodds : ∀ o ∈ odds, 0 < o)
    (acc : List ℕ) (F : List ℕ → ℝ≥0∞) :
    ∫⁻ i, credit n (decrement pop i) odds (increment acc i) F
      ∂WeightedChoice.law (weights pop odds) = credit (n + 1) pop odds acc F :=
  expectation pop odds n (request_weight_pos pop odds n hn hlen hodds) acc F

/-- A two-color urn returns the number of marked-color draws. -/
def twoColorLaw (n ones zeros a b : ℕ) : Measure ℕ :=
  (law n [ones, zeros] [a, b]).map (fun ys => ys[0]?.getD 0)

instance (n ones zeros a b : ℕ) : IsProbabilityMeasure (twoColorLaw n ones zeros a b) where
  measure_univ := by
    rw [twoColorLaw, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- The marked count is the number of zeros in the canonical two-color word. -/
theorem twoColor_word (n ones zeros a b : ℕ) :
    twoColorLaw n ones zeros a b =
      (wordLaw [ones, zeros] [a, b] n).map (fun word => word.count 0) := by
  rw [twoColorLaw, law, Measure.map_map
    (measurable_of_countable _) (measurable_of_countable _)]
  congr 1

@[simp] theorem twoColor_zero (ones zeros a b : ℕ) :
    twoColorLaw 0 ones zeros a b = Measure.dirac 0 := by
  rw [twoColor_word, wordLaw, Measure.map_dirac' (measurable_of_countable _)]
  simp

private theorem twoColor_lintegral (n ones zeros a b : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, F k ∂twoColorLaw n ones zeros a b =
      ∫⁻ word, F (word.count 0) ∂wordLaw [ones, zeros] [a, b] n := by
  rw [twoColor_word, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

/-- A two-category proportional draw is the corresponding marked-color coin. -/
theorem coin_categorical (u v : ℕ) (hs : 0 < u + v) (F : ℕ → ℝ≥0∞) :
    ∫⁻ b, F (if b then 0 else 1) ∂RealCoin.law (Urn.bias u v) =
      ∫⁻ i, F i ∂WeightedChoice.law [u, v] := by
  rw [RealCoin.lintegral_law, RealCoin.credit, Urn.pmf_true u v hs,
    Urn.pmf_false u v hs, WeightedChoice.lintegral_law]
  simp [WeightedChoice.weightedSum, ENNReal.div_eq_inv_mul]
  ring

/-- The coin only selects colors that still contain a ball. -/
theorem coin_selected (ones zeros a b : ℕ) (hs : 0 < ones * a + zeros * b) :
    ∀ᵐ marked ∂RealCoin.law (Urn.bias (ones * a) (zeros * b)),
      if marked then 0 < ones else 0 < zeros := by
  apply ae_iff_of_countable.mpr
  intro marked hm
  cases marked with
  | false =>
    change 0 < zeros
    by_contra h
    have hz := Nat.eq_zero_of_not_pos h
    apply hm
    have hp : RealCoin.pmf (Urn.bias (ones * a) (zeros * b)) false = 0 := by
      rw [Urn.pmf_false (ones * a) (zeros * b) hs]
      simp [hz]
    simpa [RealCoin.law] using hp
  | true =>
    change 0 < ones
    by_contra h
    have hz := Nat.eq_zero_of_not_pos h
    apply hm
    have hp : RealCoin.pmf (Urn.bias (ones * a) (zeros * b)) true = 0 := by
      rw [Urn.pmf_true (ones * a) (zeros * b) hs]
      simp [hz]
    simpa [RealCoin.law] using hp

/-- The two-color first-draw expectation includes empty colors and arbitrary infinite credits. -/
theorem twoColor_expectation (n ones zeros a b : ℕ) (hn : n + 1 ≤ ones + zeros)
    (ha : 0 < a) (hb : 0 < b) (F : ℕ → ℝ≥0∞) :
    ∫⁻ marked, (if marked then
        ∫⁻ k, F (k + 1) ∂twoColorLaw n (ones - 1) zeros a b
      else ∫⁻ k, F k ∂twoColorLaw n ones (zeros - 1) a b)
      ∂RealCoin.law (Urn.bias (ones * a) (zeros * b)) =
        ∫⁻ k, F k ∂twoColorLaw (n + 1) ones zeros a b := by
  have hodds : ∀ o ∈ [a, b], 0 < o := by simp [ha, hb]
  have hsWord := request_weight_pos [ones, zeros] [a, b] n (by simpa using hn) rfl hodds
  have hs : 0 < ones * a + zeros * b := by simpa [weights] using hsWord
  let K (i : ℕ) := ∫⁻ word, F ((i :: word).count 0)
    ∂wordLaw (decrement [ones, zeros] i) [a, b] n
  have hbranch (marked : Bool) :
      (if marked then ∫⁻ k, F (k + 1) ∂twoColorLaw n (ones - 1) zeros a b
        else ∫⁻ k, F k ∂twoColorLaw n ones (zeros - 1) a b) =
      K (if marked then 0 else 1) := by
    cases marked <;> simp [K, twoColor_lintegral, decrement]
  calc
    _ = ∫⁻ marked, K (if marked then 0 else 1)
        ∂RealCoin.law (Urn.bias (ones * a) (zeros * b)) :=
      lintegral_congr_ae (Filter.Eventually.of_forall hbranch)
    _ = ∫⁻ i, K i ∂WeightedChoice.law (weights [ones, zeros] [a, b]) :=
      coin_categorical (ones * a) (zeros * b) hs K
    _ = _ := by
      rw [twoColor_lintegral]
      exact word_expectation [ones, zeros] [a, b] n hsWord (fun word => F (word.count 0))

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
