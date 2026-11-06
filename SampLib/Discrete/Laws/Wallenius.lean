import SampLib.Discrete.Laws.WalleniusWords

/-! # Multivariate Wallenius law

Mapping a color word to its color counts gives the multivariate Wallenius law.
The first draw splits the expected credit by the weighted choice of its color.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.Wallenius

noncomputable section

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

end

end SampLib.Wallenius
