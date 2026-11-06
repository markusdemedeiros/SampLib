import SampLib.Discrete.Laws.NegativeBinomial
import SampLib.Discrete.Laws.MultinomialTrials

/-! # Negative-multinomial count law

Draw the total number of failures from the negative-binomial law, then allocate
those failures among the failure categories using the multinomial law.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace SampLib.NegativeMultinomial

noncomputable section

/-- Total failures, followed by their conditional allocation among categories.
Sampler validity requires `s > 0`; zero success weight uses the normalized extension. -/
def law (r s : ℕ) (ws : List ℕ) : Measure (List ℕ) :=
  (NegativeBinomial.law (Urn.bias s ws.sum) r).bind (fun n => Multinomial.law n ws)

instance (r s : ℕ) (ws : List ℕ) : IsProbabilityMeasure (law r s ws) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ
      (measurable_of_countable _).aemeasurable]
    simp

@[simp] theorem law_zero (s : ℕ) (ws : List ℕ) :
    law 0 s ws = Measure.dirac (List.replicate ws.length 0) := by
  rw [law, NegativeBinomial.law, Measure.dirac_bind (measurable_of_countable _)]
  exact Multinomial.law_zero ws

/-- The mixture retains one counter per failure category. -/
theorem length_ae (r s : ℕ) (ws : List ℕ) :
    ∀ᵐ cs ∂law r s ws, cs.length = ws.length := by
  apply ae_iff_of_countable.mpr
  intro cs hc
  by_contra hl
  apply hc
  rw [law, Measure.bind_apply (measurableSet_singleton _)
    (measurable_of_countable _).aemeasurable]
  have hz (n : ℕ) : Multinomial.law n ws {cs} = 0 := by
    by_contra hn
    exact hl ((ae_iff_of_countable.mp (Multinomial.length_ae n ws)) cs hn)
  simp_rw [hz]
  simp

@[simp] theorem law_nil (r s : ℕ) : law r s [] = Measure.dirac [] := by
  apply Measure.ext_of_singleton
  intro cs
  rw [law, Measure.bind_apply (measurableSet_singleton _)
    (measurable_of_countable _).aemeasurable]
  simp

/-- With no failure mass, every additional failure counter stays zero. -/
theorem law_zero_weights (r s : ℕ) (ws : List ℕ) (hs : 0 < s) (hz : ws.sum = 0) :
    law r s ws = Measure.dirac (List.replicate ws.length 0) := by
  have hb : Urn.bias s ws.sum = 1 := by
    apply Subtype.ext
    have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    simp [Urn.bias, hz, hs, RationalCoin.bias, hs']
  rw [law, hb, NegativeBinomial.law_one,
    Measure.dirac_bind (measurable_of_countable _), Multinomial.law_zero]

/-- Integrating the failure total exposes the canonical conditional mixture. -/
theorem mixture_expectation (r s : ℕ) (ws : List ℕ) (F : List ℕ → ℝ≥0∞) :
    ∫⁻ n, ∫⁻ cs, F cs ∂Multinomial.law n ws ∂NegativeBinomial.law (Urn.bias s ws.sum) r =
      ∫⁻ cs, F cs ∂law r s ws := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]

/-- Factor a joint count mass into its total-failure and conditional multinomial masses. -/
theorem law_singleton (r s : ℕ) (ws cs : List ℕ) (ht : 0 < ws.sum) :
    law r s ws {cs} = NegativeBinomial.law (Urn.bias s ws.sum) r {cs.sum} *
      Multinomial.law cs.sum ws {cs} := by
  rw [law, Measure.bind_apply (measurableSet_singleton _)
    (measurable_of_countable _).aemeasurable]
  have hn (n : ℕ) : Multinomial.law n ws {cs} =
      if n = cs.sum then Multinomial.law cs.sum ws {cs} else 0 := by
    by_cases h : n = cs.sum
    · subst n; simp
    · have hb : ¬(cs.length = ws.length ∧ cs.sum = n) := fun hc => h hc.2.symm
      rw [ite_eq_right h, Multinomial.law_singleton n ws cs (Or.inr ht),
        Multinomial.pmf, ite_eq_right hb]
      rfl
  calc
    _ = ∫⁻ n, ({cs.sum} : Set ℕ).indicator (fun _ => Multinomial.law cs.sum ws {cs}) n
        ∂NegativeBinomial.law (Urn.bias s ws.sum) r := by
      apply lintegral_congr
      intro n
      rw [hn]
      by_cases h : n = cs.sum <;> simp [h]
    _ = _ := by rw [lintegral_indicator_const (measurableSet_singleton _)]; exact mul_comm _ _

/-- Add an additional count vector to the current counters, in category order. -/
def addCounts (acc more : List ℕ) : List ℕ := List.zipWith Nat.add acc more

/-- Increment the selected failure counter; out-of-range indices are immaterial. -/
def increment (acc : List ℕ) (i : ℕ) : List ℕ := acc.modify i Nat.succ

theorem addCounts_increment (acc more : List ℕ) (i : ℕ) :
    addCounts acc (increment more i) = addCounts (increment acc i) more := by
  induction acc generalizing more i with
  | nil => simp [addCounts, increment]
  | cons a acc IH =>
    cases more with
    | nil => simp [addCounts, increment]
    | cons b more =>
      cases i with
      | zero => simp [addCounts, increment, Nat.add_comm, Nat.add_left_comm]
      | succ i =>
        simpa [addCounts, increment] using congrArg (List.cons (a + b)) (IH more i)

/-- The output credit after completing the requested successes. -/
def credit (r s : ℕ) (ws acc : List ℕ) (F : List ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ more, F (addCounts acc more) ∂law r s ws

private theorem addCounts_zeros (acc : List ℕ) :
    addCounts acc (List.replicate acc.length 0) = acc := by
  induction acc with
  | nil => rfl
  | cons a acc IH => simpa [addCounts, List.replicate_succ] using congrArg (List.cons a) IH

@[simp] theorem credit_zero (s : ℕ) (ws acc : List ℕ) (h : acc.length = ws.length)
    (F : List ℕ → ℝ≥0∞) : credit 0 s ws acc F = F acc := by
  rw [credit, law_zero, lintegral_dirac]
  rw [← h, addCounts_zeros]

private theorem zeros_addCounts (more : List ℕ) :
    addCounts (List.replicate more.length 0) more = more := by
  induction more with
  | nil => rfl
  | cons a more IH =>
    simpa [addCounts, List.replicate_succ] using congrArg (List.cons a) IH

/-- The initial zero counters leave the canonical continuation credit unchanged. -/
theorem credit_initial (r s : ℕ) (ws : List ℕ) (F : List ℕ → ℝ≥0∞) :
    credit r s ws (List.replicate ws.length 0) F = ∫⁻ cs, F cs ∂law r s ws := by
  rw [credit]
  apply lintegral_congr_ae
  filter_upwards [length_ae r s ws] with cs hcs
  rw [← hcs, zeros_addCounts]

end

end SampLib.NegativeMultinomial
