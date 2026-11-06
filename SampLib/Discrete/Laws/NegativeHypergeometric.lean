import Metrology.ProbLang.Discrete
import SampLib.Discrete.Laws.Hypergeometric

/-! # Negative hypergeometric law

Reading a uniformly permuted labelled urn counts the unmarked balls before the
requested marked ball. The first-color partition gives the expectation recurrence.
-/

open scoped ENNReal

namespace SampLib.NegativeHypergeometric

noncomputable section

open MeasureTheory Measure SampleWithoutReplacement

/-- Count unmarked entries before the requested marked entry. -/
def failures : ℕ → List Bool → ℕ
  | 0, _ => 0
  | _, [] => 0
  | r + 1, true :: xs => failures r xs
  | r + 1, false :: xs => failures (r + 1) xs + 1

/-- Uniform random ordering of the input positions, decoded to their values. -/
def wordLaw (xs : List Bool) : Measure (List Bool) :=
  (SampleWithoutReplacement.law xs xs.length).map (selected xs xs.length)

instance (xs : List Bool) : IsProbabilityMeasure (wordLaw xs) := by
  let : Fact (xs.length ≤ xs.length) := ⟨le_rfl⟩
  constructor
  rw [wordLaw, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
  simp

/-- Negative-hypergeometric count from a uniform ordering of labelled balls. -/
def law (r ones zeros : ℕ) : Measure ℕ :=
  (wordLaw (Hypergeometric.urn ones zeros)).map (failures r)

instance (r ones zeros : ℕ) : IsProbabilityMeasure (law r ones zeros) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

@[simp] theorem expectation_zero (ones zeros : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, F k ∂law 0 ones zeros = F 0 := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  simp [failures]

/-- Every position is equally likely to be first in a uniform ordering. -/
theorem word_expectation (xs : List Bool) (h : xs ≠ []) (F : List Bool → ℝ≥0∞) :
    ∫⁻ ys, F ys ∂wordLaw xs =
      (∑ i : Fin xs.length, ∫⁻ ys, F (xs.get i :: ys) ∂wordLaw (xs.eraseIdx i)) /
        xs.length := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons x xs =>
      rw [wordLaw, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
      change (∫⁻ t, F (selected (x :: xs) (xs.length + 1) t)
        ∂SampleWithoutReplacement.law (x :: xs) (xs.length + 1)) = _
      rw [SampleWithoutReplacement.expectation]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [wordLaw, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
      simp only [selected]
      rw [show ((x :: xs).eraseIdx i.val).length = xs.length from by
        simpa using List.length_eraseIdx_of_lt i.isLt]

private theorem erase_true (ones zeros i : ℕ) (hi : i < ones) :
    (Hypergeometric.urn ones zeros).eraseIdx i = Hypergeometric.urn (ones - 1) zeros := by
  unfold Hypergeometric.urn
  rw [List.eraseIdx_append_of_lt_length (l := List.replicate ones true) (by simpa using hi)]
  simp [List.eraseIdx_replicate, hi]

private theorem erase_false (ones zeros i : ℕ) (hi : ones ≤ i) (hib : i < ones + zeros) :
    (Hypergeometric.urn ones zeros).eraseIdx i = Hypergeometric.urn ones (zeros - 1) := by
  have hz : i - ones < zeros := by omega
  unfold Hypergeometric.urn
  rw [List.eraseIdx_append_of_length_le (l := List.replicate ones true) (by simpa using hi)]
  simp [List.eraseIdx_replicate, hz]

/-- Partition permutations according to the first marked or unmarked ball. -/
theorem expectation (r ones zeros : ℕ) (ho : 0 < ones) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, F k ∂law (r + 1) ones zeros =
      ((ones : ℝ≥0∞) * (∫⁻ k, F k ∂law r (ones - 1) zeros) +
        (zeros : ℝ≥0∞) * (∫⁻ k, F (k + 1) ∂law (r + 1) ones (zeros - 1))) /
          (ones + zeros) := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  rw [word_expectation _ (List.ne_nil_of_length_pos (by
    simpa using (show 0 < ones + zeros by omega)))]
  have hstep (i : Fin (Hypergeometric.urn ones zeros).length) :
      (∫⁻ ys, F (failures (r + 1) ((Hypergeometric.urn ones zeros).get i :: ys))
        ∂wordLaw ((Hypergeometric.urn ones zeros).eraseIdx i)) =
      if i.val < ones then ∫⁻ k, F k ∂law r (ones - 1) zeros
      else ∫⁻ k, F (k + 1) ∂law (r + 1) ones (zeros - 1) := by
    by_cases hi : i.val < ones
    · have hget : (Hypergeometric.urn ones zeros).get i = true := by
        rw [List.get_eq_getElem]
        simp [Hypergeometric.urn, hi]
      simp only [hi, ite_true, hget, failures]
      rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
      rw [erase_true ones zeros i hi]
    · have hib : i.val < ones + zeros := by simpa using i.isLt
      have hget : (Hypergeometric.urn ones zeros).get i = false := by
        rw [List.get_eq_getElem]
        simp [Hypergeometric.urn, List.getElem_append, hi]
      simp only [hi, ite_false, hget, failures]
      rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
      rw [erase_false ones zeros i (by omega) hib]
  simp_rw [hstep]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < ones then
    ∫⁻ k, F k ∂law r (ones - 1) zeros else ∫⁻ k, F (k + 1) ∂law (r + 1) ones (zeros - 1))]
  simp only [Hypergeometric.urn_length]
  rw [Finset.sum_range_add]
  simp [Finset.sum_ite_of_true, Nat.not_lt.mpr (Nat.le_add_right ones _), nsmul_eq_mul]

/-- Credit after the first color in the permuted urn. -/
def continuation (r ones zeros : ℕ) (F : ℕ → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then ∫⁻ k, F k ∂law r (ones - 1) zeros
  else ∫⁻ k, F (k + 1) ∂law (r + 1) ones (zeros - 1)

/-- The first marked/unmarked partition is the input coin's expectation. -/
theorem expectation_coin (r ones zeros : ℕ) (ho : 0 < ones) (F : ℕ → ℝ≥0∞) :
    ∫⁻ b, continuation r ones zeros F b ∂RealCoin.law (Urn.bias ones zeros) =
      ∫⁻ k, F k ∂law (r + 1) ones zeros := by
  have ht : 0 < ones + zeros := by omega
  rw [RealCoin.lintegral_law, RealCoin.credit, Urn.pmf_true ones zeros ht,
    Urn.pmf_false ones zeros ht, expectation r ones zeros ho]
  simp only [continuation, ite_true, Bool.false_eq_true, ite_false,
    ENNReal.div_eq_inv_mul]
  ring

/-- An unmarked draw has positive probability only when unmarked balls remain. -/
theorem possible_failure (ones zeros : ℕ) (ho : 0 < ones) :
    ∀ᵐ b ∂RealCoin.law (Urn.bias ones zeros), b = false → 0 < zeros := by
  by_cases hz : zeros = 0
  · subst zeros
    have hb : Urn.bias ones 0 = 1 := by
      apply Subtype.ext
      simp [Urn.bias, ho, RationalCoin.bias, ho.ne']
    simp [hb, RealCoin.law, RealCoin.pmf]
  · exact Filter.Eventually.of_forall fun _ _ => Nat.pos_of_ne_zero hz

end

end SampLib.NegativeHypergeometric
