import SampLib.Discrete.Laws.MultinomialPmf

/-! # The multinomial count law

Sampling one category at a time with binomial thinning gives a kernel whose
atoms are the multinomial masses. The law therefore splits along its first
category for every continuation credit.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace SampLib.Multinomial

noncomputable section

private def kernel (n : ℕ) : List ℕ → Measure (List ℕ)
  | [] => Measure.dirac []
  | w :: ws => (Binomial.law (Urn.bias w ws.sum) n).bind
      (fun k => (kernel (n - k) ws).map (List.cons k))

private instance kernel_probability (n : ℕ) (ws : List ℕ) :
    IsProbabilityMeasure (kernel n ws) := by
  induction ws generalizing n with
  | nil => dsimp [kernel]; infer_instance
  | cons w ws IH =>
    constructor
    rw [kernel, Measure.bind_apply MeasurableSet.univ
      (measurable_of_countable _).aemeasurable]
    have hm (k : ℕ) : ((kernel (n - k) ws).map (List.cons k)) Set.univ = 1 := by
      rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
      simp only [Set.preimage_univ]
      exact (IH (n - k)).measure_univ
    simp_rw [hm]
    simp

private theorem kernel_expectation (n w : ℕ) (ws : List ℕ)
    (F : List ℕ → ℝ≥0∞) :
    ∫⁻ k, ∫⁻ cs, F (k :: cs) ∂kernel (n - k) ws ∂Binomial.law (Urn.bias w ws.sum) n =
      ∫⁻ cs, F cs ∂kernel n (w :: ws) := by
  rw [kernel, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]
  simp_rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

private theorem kernel_nil_singleton (n w : ℕ) (ws : List ℕ) :
    kernel n (w :: ws) {[]} = 0 := by
  rw [kernel, Measure.bind_apply (measurableSet_singleton _)
    (measurable_of_countable _).aemeasurable]
  have he (k : ℕ) : List.cons k ⁻¹' ({[]} : Set (List ℕ)) = ∅ := by ext cs; simp
  simp [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _), he]

private theorem kernel_cons_singleton (n w : ℕ) (ws : List ℕ) (k : ℕ) (cs : List ℕ) :
    kernel n (w :: ws) {k :: cs} =
      Binomial.law (Urn.bias w ws.sum) n {k} * kernel (n - k) ws {cs} := by
  rw [kernel, Measure.bind_apply (measurableSet_singleton _)
    (measurable_of_countable _).aemeasurable]
  have he (i : ℕ) : List.cons i ⁻¹' ({k :: cs} : Set (List ℕ)) =
      if i = k then {cs} else ∅ := by
    ext xs
    by_cases hi : i = k <;> simp [hi]
  calc
    _ = ∫⁻ i, ({k} : Set ℕ).indicator (fun _ => kernel (n - k) ws {cs}) i
        ∂Binomial.law (Urn.bias w ws.sum) n := by
      apply lintegral_congr
      intro i
      rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _), he]
      by_cases hi : i = k <;> simp [hi]
    _ = _ := by rw [lintegral_indicator_const (measurableSet_singleton _)]; exact mul_comm _ _

private theorem kernel_zero (ws : List ℕ) :
    kernel 0 ws = Measure.dirac (List.replicate ws.length 0) := by
  induction ws with
  | nil => rfl
  | cons w ws IH =>
    rw [kernel, Binomial.law, Measure.dirac_bind (measurable_of_countable _)]
    simp [IH, List.replicate_succ]

private theorem bias_full (w : ℕ) (hw : 0 < w) : Urn.bias w 0 = 1 := by
  apply Subtype.ext
  have hR : (w : ℝ) ≠ 0 := by exact_mod_cast hw.ne'
  simp [Urn.bias, hw, RationalCoin.bias, hR]

private theorem kernel_full (n w : ℕ) (ws : List ℕ) (hw : 0 < w) (hz : ws.sum = 0) :
    kernel n (w :: ws) = Measure.dirac (n :: List.replicate ws.length 0) := by
  rw [kernel, hz, bias_full w hw, Binomial.law_one,
    Measure.dirac_bind (measurable_of_countable _)]
  simp [kernel_zero]

private theorem kernel_zero_weights (n : ℕ) (ws : List ℕ) (h : ws.sum = 0) :
    kernel n ws = Measure.dirac (List.replicate ws.length 0) := by
  induction ws generalizing n with
  | nil => rfl
  | cons w ws IH =>
    have hw : w = 0 ∧ ws.sum = 0 := by simpa using h
    rw [kernel, hw.1, hw.2]
    simp only [Urn.bias, Nat.zero_add, lt_self_iff_false, dite_false, Binomial.law_zero]
    rw [Measure.dirac_bind (measurable_of_countable _)]
    simp [IH n hw.2, List.replicate_succ]

private theorem kernel_singleton (ws : List ℕ) :
    ∀ n, n = 0 ∨ 0 < ws.sum → ∀ cs, kernel n ws {cs} = (pmf n ws cs : ℝ≥0∞) := by
  induction ws with
  | nil =>
    intro n h cs
    have hn : n = 0 := by simpa using h
    subst n
    simp only [kernel, dirac_singleton, pmf_zero, List.length_nil, List.replicate_zero]
  | cons w ws IH =>
    intro n h cs
    by_cases hn : n = 0
    · subst n
      rw [kernel_zero, dirac_singleton, pmf_zero]
    · have ht : 0 < w + ws.sum := by simpa using h.resolve_left hn
      by_cases ht' : 0 < ws.sum
      · cases cs with
        | nil => rw [kernel_nil_singleton]; simp [pmf]
        | cons k cs =>
          rw [kernel_cons_singleton]
          by_cases hk : k ≤ n
          · rw [IH (n - k) (Or.inr ht') cs, binomial_singleton n w ws.sum k ht]
            by_cases hc : cs.length = ws.length ∧ cs.sum = n - k
            · have hs : k + cs.sum = n := by omega
              simpa only [ENNReal.coe_mul] using congrArg (fun p : ℝ≥0 => (p : ℝ≥0∞))
                (pmf_cons n w k ws cs ht hc.1 hs).symm
            · have hb : ¬ ((k :: cs).length = (w :: ws).length ∧ (k :: cs).sum = n) := by
                intro hcs
                apply hc
                constructor
                · simpa using hcs.1
                · have hs : k + cs.sum = n := by simpa using hcs.2
                  omega
              rw [pmf_of_invalid _ _ _ hb, pmf_of_invalid _ _ _ hc]
              simp
          · have hm : Binomial.law (Urn.bias w ws.sum) n {k} = 0 := by
              rw [Binomial.law_singleton]
              simp [Nat.choose_eq_zero_of_lt (lt_of_not_ge hk)]
            have hb : ¬ ((k :: cs).length = (w :: ws).length ∧ (k :: cs).sum = n) := by
              intro hcs
              have hs : k + cs.sum = n := by simpa using hcs.2
              omega
            rw [hm, pmf_of_invalid _ _ _ hb]
            simp
      · have hz : ws.sum = 0 := by omega
        have hw : 0 < w := by omega
        rw [kernel_full n w ws hw hz, dirac_singleton, pmf_full n w ws cs hw hz]

private theorem rawLaw_singleton (n : ℕ) (ws cs : List ℕ) :
    rawLaw n ws {cs} = (pmf n ws cs : ℝ≥0∞) := by
  rw [rawLaw, Measure.sum_apply _ (measurableSet_singleton _)]
  classical
  rw [tsum_eq_single cs]
  · simp
  · intro xs hxs
    simp [Measure.smul_apply, hxs]

private theorem law_eq_kernel (n : ℕ) (ws : List ℕ) : law n ws = kernel n ws := by
  by_cases h : n = 0 ∨ 0 < ws.sum
  · rw [law, ite_eq_left h]
    apply Measure.ext_of_singleton
    intro cs
    rw [rawLaw_singleton, kernel_singleton ws n h cs]
  · have hz : ws.sum = 0 := by omega
    rw [law, ite_eq_right h, kernel_zero_weights n ws hz]

instance (n : ℕ) (ws : List ℕ) : IsProbabilityMeasure (law n ws) := by
  rw [law_eq_kernel]
  infer_instance

/-- The standard multinomial masses sum to one on the complete valid domain. -/
theorem tsum_pmf (n : ℕ) (ws : List ℕ) (h : n = 0 ∨ 0 < ws.sum) :
    ∑' cs, (pmf n ws cs : ℝ≥0∞) = 1 := by
  have hm : law n ws Set.univ = 1 := measure_univ
  rw [law, ite_eq_left h, rawLaw, Measure.sum_apply _ MeasurableSet.univ] at hm
  simpa [Measure.smul_apply] using hm

/-- The standard multinomial formula, with zero mass outside length/sum support. -/
theorem law_singleton (n : ℕ) (ws cs : List ℕ) (h : n = 0 ∨ 0 < ws.sum) :
    law n ws {cs} = (pmf n ws cs : ℝ≥0∞) := by
  rw [law_eq_kernel, kernel_singleton ws n h cs]

@[simp] theorem law_zero (ws : List ℕ) :
    law 0 ws = Measure.dirac (List.replicate ws.length 0) := by
  rw [law_eq_kernel, kernel_zero]

@[simp] theorem law_nil (n : ℕ) : law n [] = Measure.dirac [] := by
  rw [law_eq_kernel]
  rfl

@[simp] theorem expectation_zero (ws : List ℕ) (F : List ℕ → ℝ≥0∞) :
    ∫⁻ cs, F cs ∂law 0 ws = F (List.replicate ws.length 0) := by simp

@[simp] theorem expectation_nil (n : ℕ) (F : List ℕ → ℝ≥0∞) :
    ∫⁻ cs, F cs ∂law n [] = F [] := by simp

/-- Condition on the first count, then distribute the remaining trials among the tail categories. -/
theorem expectation (n w : ℕ) (ws : List ℕ) (F : List ℕ → ℝ≥0∞) :
    ∫⁻ k, ∫⁻ cs, F (k :: cs) ∂law (n - k) ws ∂Binomial.law (Urn.bias w ws.sum) n =
      ∫⁻ cs, F cs ∂law n (w :: ws) := by
  simp_rw [law_eq_kernel]
  exact kernel_expectation n w ws F

/-- The selected count is feasible and leaves a valid tail problem almost surely. -/
theorem split_support (n w : ℕ) (ws : List ℕ) (h : n = 0 ∨ 0 < (w :: ws).sum) :
    ∀ᵐ k ∂Binomial.law (Urn.bias w ws.sum) n,
      k ≤ n ∧ (n - k = 0 ∨ 0 < ws.sum) := by
  by_cases ht : 0 < ws.sum
  · filter_upwards [Binomial.support (Urn.bias w ws.sum) n] with k hk
    exact ⟨hk, Or.inr ht⟩
  · have hz : ws.sum = 0 := by omega
    rcases h with rfl | h
    · simp [Binomial.law]
    · have hw : 0 < w := by simpa [hz] using h
      rw [hz, bias_full w hw, Binomial.law_one]
      simp

end

end SampLib.Multinomial
