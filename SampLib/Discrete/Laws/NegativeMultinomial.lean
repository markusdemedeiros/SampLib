import SampLib.Discrete.Laws.NegativeBinomialStep
import SampLib.Discrete.Laws.MultinomialTrials

/-! # Negative-multinomial category counts

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

private theorem addCounts_increment (acc more : List ℕ) (i : ℕ) :
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

/-- The finite amplification factor used by the categorical loop. -/
def factor (s : ℕ) (ws : List ℕ) : ℝ≥0 := 1 + unitInterval.toNNReal (Urn.bias s ws.sum)

private theorem success_pos (s : ℕ) (ws : List ℕ) (hs : 0 < s) :
    0 < (Urn.bias s ws.sum : ℝ) := by
  have ht : 0 < s + ws.sum := by omega
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have ht' : (0 : ℝ) < (s : ℝ) + ws.sum := by exact_mod_cast ht
  simpa only [Urn.bias, dite_eq_left ht, RationalCoin.bias, Int.cast_natCast,
    Int.cast_add] using div_pos hs' ht'

theorem one_lt_factor (s : ℕ) (ws : List ℕ) (hs : 0 < s) : 1 < factor s ws := by
  apply lt_add_of_pos_right
  exact_mod_cast success_pos s ws hs

/-- The remaining success target after one categorical draw. -/
def nextRemaining (r : ℕ) : ℕ → ℕ
  | 0 => r - 1
  | _ + 1 => r

/-- The first category lowers the target; all failure categories retain it. -/
theorem mean_remaining (r s : ℕ) (ws : List ℕ) (hs : 0 < s) :
    ∫⁻ i, (nextRemaining r i : ℝ≥0∞) ∂WeightedChoice.law (s :: ws) =
      RealCoin.pmf (Urn.bias s ws.sum) true * ((r - 1 : ℕ) : ℝ≥0∞) +
        RealCoin.pmf (Urn.bias s ws.sum) false * r := by
  have ht : 0 < s + ws.sum := by omega
  rw [WeightedChoice.lintegral_law]
  change ((s : ℝ≥0∞) * ((r - 1 : ℕ) : ℝ≥0∞) +
    WeightedChoice.weightedSum ws (fun _ => (r : ℝ≥0∞))) /
      ((s + ws.sum : ℕ) : ℝ≥0∞) = _
  rw [WeightedChoice.weightedSum_const, Urn.pmf_true s ws.sum ht,
    Urn.pmf_false s ws.sum ht]
  simp only [Nat.cast_add, div_eq_mul_inv]
  ring

private theorem factor_coe (s : ℕ) (ws : List ℕ) :
    (factor s ws : ℝ≥0∞) = 1 + RealCoin.pmf (Urn.bias s ws.sum) true := by
  simp [factor, ENNReal.coe_nnreal_eq, RealCoin.pmf,
    ENNReal.ofReal_add zero_le_one (Urn.bias s ws.sum).2.1]

/-- The finite remaining-work potential leaves one unit for fixed amplification. -/
theorem termination_identity (r s : ℕ) (ws : List ℕ) (hr : 0 < r) (hs : 0 < s) :
    (∫⁻ i, (nextRemaining r i : ℝ≥0∞) ∂WeightedChoice.law (s :: ws)) +
        factor s ws = (r : ℝ≥0∞) + 1 := by
  have hR : (r : ℝ≥0∞) = ((r - 1 : ℕ) : ℝ≥0∞) + 1 := by
    exact_mod_cast (show r = r - 1 + 1 by omega)
  rw [mean_remaining r s ws hs, factor_coe]
  calc
    _ = (RealCoin.pmf (Urn.bias s ws.sum) true + RealCoin.pmf (Urn.bias s ws.sum) false) *
          ((r - 1 : ℕ) : ℝ≥0∞) +
        (RealCoin.pmf (Urn.bias s ws.sum) true + RealCoin.pmf (Urn.bias s ws.sum) false) + 1 :=
      by rw [hR]; ring
    _ = _ := by
      rw [RealCoin.pmf_sum, one_mul]
      exact congrArg (fun x => x + 1) hR.symm

private theorem credit_mixture (r s : ℕ) (ws acc : List ℕ) (F : List ℕ → ℝ≥0∞) :
    credit r s ws acc F = ∫⁻ n, ∫⁻ more, F (addCounts acc more) ∂Multinomial.law n ws
      ∂NegativeBinomial.law (Urn.bias s ws.sum) r :=
  (mixture_expectation r s ws (fun more => F (addCounts acc more))).symm

private theorem credit_renewal (r s : ℕ) (ws acc : List ℕ) (hs : 0 < s)
    (ht : 0 < ws.sum) (F : List ℕ → ℝ≥0∞) :
    credit (r + 1) s ws acc F =
      RealCoin.pmf (Urn.bias s ws.sum) true * credit r s ws acc F +
        RealCoin.pmf (Urn.bias s ws.sum) false *
          (∫⁻ j, credit (r + 1) s ws (increment acc j) F ∂WeightedChoice.law ws) := by
  have hfail : (∫⁻ n, ∫⁻ more, F (addCounts acc more) ∂Multinomial.law (n + 1) ws
      ∂NegativeBinomial.law (Urn.bias s ws.sum) (r + 1)) =
      ∫⁻ j, credit (r + 1) s ws (increment acc j) F ∂WeightedChoice.law ws := by
    calc
      _ = ∫⁻ n, ∫⁻ j, ∫⁻ more, F (addCounts acc (increment more j))
          ∂Multinomial.law n ws ∂WeightedChoice.law ws
          ∂NegativeBinomial.law (Urn.bias s ws.sum) (r + 1) :=
        lintegral_congr fun n =>
          (Multinomial.trial_expectation n ws ht (fun more => F (addCounts acc more))).symm
      _ = ∫⁻ j, ∫⁻ n, ∫⁻ more, F (addCounts (increment acc j) more)
          ∂Multinomial.law n ws ∂NegativeBinomial.law (Urn.bias s ws.sum) (r + 1)
          ∂WeightedChoice.law ws := by
        rw [lintegral_lintegral_swap (measurable_of_countable _).aemeasurable]
        simp_rw [addCounts_increment]
      _ = _ := lintegral_congr fun j => (credit_mixture (r + 1) s ws (increment acc j) F).symm
  rw [credit_mixture (r + 1) s ws acc F,
    NegativeBinomial.expectation_step (Urn.bias s ws.sum) (success_pos s ws hs) r
      (fun n => ∫⁻ more, F (addCounts acc more) ∂Multinomial.law n ws),
    ← credit_mixture r s ws acc F, hfail]

/-- The distribution credit after one success or one failure-category increment. -/
def nextCredit (r s : ℕ) (ws acc : List ℕ) (F : List ℕ → ℝ≥0∞) : ℕ → ℝ≥0∞
  | 0 => credit (r - 1) s ws acc F
  | j + 1 => credit r s ws (increment acc j) F

/-- The canonical mixture satisfies the categorical stopping recurrence. -/
theorem expectation (r s : ℕ) (ws acc : List ℕ) (hr : 0 < r) (hs : 0 < s)
    (F : List ℕ → ℝ≥0∞) :
    ∫⁻ i, nextCredit r s ws acc F i ∂WeightedChoice.law (s :: ws) = credit r s ws acc F := by
  cases r with
  | zero => omega
  | succ r =>
    by_cases ht : 0 < ws.sum
    · rw [WeightedChoice.split_expectation s ws ht]
      change RealCoin.pmf (Urn.bias s ws.sum) true * credit r s ws acc F +
        RealCoin.pmf (Urn.bias s ws.sum) false *
          (∫⁻ j, credit (r + 1) s ws (increment acc j) F ∂WeightedChoice.law ws) = _
      exact (credit_renewal r s ws acc hs ht F).symm
    · have hz : ws.sum = 0 := by omega
      have hc (k : ℕ) : credit k s ws acc F = F (addCounts acc (List.replicate ws.length 0)) := by
        rw [credit, law_zero_weights k s ws hs hz, lintegral_dirac]
      rw [WeightedChoice.zero_tail_expectation s ws hs hz]
      change credit r s ws acc F = credit (r + 1) s ws acc F
      rw [hc, hc]

/-- The reusable one-step credit kernel for the categorical stopping loop. -/
def stepCredit (r s : ℕ) (ws acc : List ℕ) (F : List ℕ → ℝ≥0∞) (δ : ℝ≥0∞)
    (i : ℕ) : ℝ≥0∞ :=
  nextCredit r s ws acc F i + (nextRemaining r i : ℝ≥0∞) * δ + factor s ws * δ

/-- Preserve distribution and finite-work credits, including infinite continuations and slack. -/
theorem conservation (r s : ℕ) (ws acc : List ℕ) (hr : 0 < r) (hs : 0 < s)
    (F : List ℕ → ℝ≥0∞) (δ : ℝ≥0∞) :
    ∫⁻ i, stepCredit r s ws acc F δ i ∂WeightedChoice.law (s :: ws) =
      credit r s ws acc F + (r : ℝ≥0∞) * δ + δ := by
  simp only [stepCredit]
  let : NeZero (s :: ws).sum := ⟨by simp only [List.sum_cons]; omega⟩
  rw [lintegral_add_left (measurable_of_countable _),
    lintegral_add_left (measurable_of_countable _), expectation r s ws acc hr hs F,
    lintegral_mul_const _ (measurable_of_countable _), lintegral_const, measure_univ, mul_one]
  calc
    _ = credit r s ws acc F +
        ((∫⁻ i, (nextRemaining r i : ℝ≥0∞) ∂WeightedChoice.law (s :: ws)) + factor s ws) * δ :=
      by ring
    _ = _ := by rw [termination_identity r s ws hr hs]; ring

end

end SampLib.NegativeMultinomial
