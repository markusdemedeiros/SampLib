import SampLib.Discrete.Laws.BinomialThinning
import SampLib.Common.Laws.Urn
import SampLib.Discrete.Laws.MultinomialCoefficients

/-! # The multinomial count law

Count vectors have one coordinate per category and total `n`. Their standard
multinomial masses determine the law independently of conditional sampling.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace SampLib.Multinomial

noncomputable section

/-- The product of the category weights raised to their respective counts. -/
def weightProduct (ws cs : List ℕ) : ℝ≥0 :=
  (ws.zipWith (fun (w c : ℕ) => (w : ℝ≥0) ^ c) cs).prod

@[simp] theorem weightProduct_cons (w c : ℕ) (ws cs : List ℕ) :
    weightProduct (w :: ws) (c :: cs) = (w : ℝ≥0) ^ c * weightProduct ws cs := rfl

/-- The usual multinomial mass, with zero mass outside the count-vector support. -/
def pmf (n : ℕ) (ws cs : List ℕ) : ℝ≥0 :=
  if cs.length = ws.length ∧ cs.sum = n then
    cs.multinomial * weightProduct ws cs / (ws.sum : ℝ≥0) ^ n
  else 0

private theorem pmf_of_invalid (n : ℕ) (ws cs : List ℕ)
    (h : ¬(cs.length = ws.length ∧ cs.sum = n)) : pmf n ws cs = 0 := ite_eq_right h

private theorem dirac_singleton (a b : List ℕ) :
    (Measure.dirac a : Measure (List ℕ)) {b} =
      ((if b = a then 1 else 0 : ℝ≥0) : ℝ≥0∞) := by
  by_cases h : b = a <;> simp [h]

private def rawLaw (n : ℕ) (ws : List ℕ) : Measure (List ℕ) :=
  Measure.sum (fun cs => (pmf n ws cs : ℝ≥0∞) • Measure.dirac cs)

/-- The canonical multinomial law. Invalid positive-trial, zero-weight inputs use
an arbitrary zero-vector extension; sampler specifications exclude that case. -/
def law (n : ℕ) (ws : List ℕ) : Measure (List ℕ) :=
  if n = 0 ∨ 0 < ws.sum then rawLaw n ws
  else Measure.dirac (List.replicate ws.length 0)

private theorem counts_zero (cs : List ℕ) (h : cs.sum = 0) :
    cs = List.replicate cs.length 0 := by
  induction cs with
  | nil => rfl
  | cons c cs IH =>
    simp only [List.sum_cons, Nat.add_eq_zero_iff] at h
    simpa [List.replicate_succ, h.1] using congrArg (List.cons 0) (IH h.2)

private theorem multinomial_zeros (m : ℕ) : (List.replicate m 0).multinomial = 1 := by
  induction m with
  | zero => rfl
  | succ m IH => simp [List.replicate_succ, List.multinomial_cons, IH]

@[simp] theorem weightProduct_zeros (ws : List ℕ) :
    weightProduct ws (List.replicate ws.length 0) = 1 := by
  induction ws with
  | nil => rfl
  | cons w ws IH =>
    simpa only [List.length_cons, List.replicate_succ, weightProduct_cons, pow_zero,
      one_mul] using IH

private theorem weightProduct_zero_total (ws cs : List ℕ) (hw : ws.sum = 0)
    (hl : cs.length = ws.length) :
    weightProduct ws cs = if cs.sum = 0 then 1 else 0 := by
  induction ws generalizing cs with
  | nil => cases cs <;> simp_all [weightProduct]
  | cons w ws IH =>
    cases cs with
    | nil => simp at hl
    | cons c cs =>
      have hw' : w = 0 ∧ ws.sum = 0 := by simpa using hw
      have hl' : cs.length = ws.length := by simpa using hl
      by_cases hc : c = 0
      · simp only [weightProduct_cons, hw'.1, hc, pow_zero, one_mul,
          List.sum_cons, Nat.zero_add, IH cs hw'.2 hl']
      · simp [weightProduct, hw'.1, hc, Nat.add_eq_zero_iff]

@[simp] theorem pmf_zero (ws cs : List ℕ) :
    pmf 0 ws cs = if cs = List.replicate ws.length 0 then 1 else 0 := by
  by_cases h : cs.length = ws.length ∧ cs.sum = 0
  · have he : cs = List.replicate ws.length 0 := by rw [counts_zero cs h.2, h.1]
    simp [pmf, he, multinomial_zeros]
  · have he : cs ≠ List.replicate ws.length 0 := by
      intro he
      apply h
      simp [he]
    simp [pmf, h, he]

private def binomialPmf (n w t k : ℕ) : ℝ≥0 :=
  n.choose k * ((w : ℝ≥0) / ((w + t : ℕ) : ℝ≥0)) ^ k *
    ((t : ℝ≥0) / ((w + t : ℕ) : ℝ≥0)) ^ (n - k)

private theorem binomial_singleton (n w t k : ℕ) (ht : 0 < w + t) :
    Binomial.law (Urn.bias w t) n {k} = (binomialPmf n w t k : ℝ≥0∞) := by
  have hd : (w : ℝ≥0) + t ≠ 0 := by exact_mod_cast ht.ne'
  rw [Binomial.law_singleton, Urn.pmf_true w t ht, Urn.pmf_false w t ht]
  simp only [binomialPmf, ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_div hd,
    ENNReal.coe_natCast, ENNReal.coe_add, Nat.cast_add]

/-- The multinomial coefficient and weight monomial split at the first category. -/
private theorem pmf_cons (n w k : ℕ) (ws cs : List ℕ) (ht : 0 < w + ws.sum)
    (hl : cs.length = ws.length) (hs : k + cs.sum = n) :
    pmf n (w :: ws) (k :: cs) = binomialPmf n w ws.sum k * pmf (n - k) ws cs := by
  subst n
  have hwhole : (k :: cs).length = (w :: ws).length ∧
      (k :: cs).sum = k + cs.sum := by simp [hl]
  have htail : cs.length = ws.length ∧ cs.sum = k + cs.sum - k := by simp [hl]
  have hd : (w : ℝ≥0) + ws.sum ≠ 0 := by exact_mod_cast ht.ne'
  rw [pmf, ite_eq_left hwhole, pmf, ite_eq_left htail, List.multinomial_cons]
  simp only [weightProduct_cons, List.sum_cons, Nat.cast_mul, Nat.cast_add,
    binomialPmf, Nat.add_sub_cancel_left]
  by_cases hz : (ws.sum : ℝ≥0) ^ cs.sum = 0
  · have hw : ws.sum = 0 := by exact_mod_cast (pow_eq_zero_iff'.mp hz).1
    have hc : cs.sum ≠ 0 := (pow_eq_zero_iff'.mp hz).2
    have hp : weightProduct ws cs = 0 := by
      rw [weightProduct_zero_total ws cs hw hl, ite_eq_right hc]
    simp [hp]
  · rw [div_pow, div_pow, pow_add]
    field_simp [hd, hz]

private theorem pmf_full (n w : ℕ) (ws cs : List ℕ) (hw : 0 < w) (hz : ws.sum = 0) :
    pmf n (w :: ws) cs = if cs = n :: List.replicate ws.length 0 then 1 else 0 := by
  cases cs with
  | nil => simp [pmf]
  | cons k cs =>
    by_cases hl : cs.length = ws.length
    · by_cases hs : k + cs.sum = n
      · by_cases hc : cs.sum = 0
        · have he : cs = List.replicate ws.length 0 := by rw [counts_zero cs hc, hl]
          have hk : k = n := by omega
          have hw' : (w : ℝ≥0) ≠ 0 := by exact_mod_cast hw.ne'
          subst k
          rw [he]
          simp [pmf, List.multinomial_cons, multinomial_zeros, hz, hw']
        · have hp : weightProduct ws cs = 0 := by
            rw [weightProduct_zero_total ws cs hz hl, ite_eq_right hc]
          have he : k :: cs ≠ n :: List.replicate ws.length 0 := by
            intro he
            rcases List.cons.inj he with ⟨rfl, rfl⟩
            simp at hc
          simp [pmf, hl, hs, hp, he]
      · have he : k :: cs ≠ n :: List.replicate ws.length 0 := by
          intro he
          rcases List.cons.inj he with ⟨rfl, rfl⟩
          simp at hs
        simp [pmf, hl, hs, he]
    · have he : k :: cs ≠ n :: List.replicate ws.length 0 := by
        intro he
        rcases List.cons.inj he with ⟨rfl, rfl⟩
        simp at hl
      simp [pmf, hl, he]

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
