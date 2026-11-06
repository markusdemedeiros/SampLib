import SampLib.Discrete.Laws.BinomialThinning
import SampLib.Common.Laws.Urn
import SampLib.Discrete.Laws.MultinomialCoefficients

/-! # Multinomial masses

Count vectors have one coordinate per category and total `n`. Their standard
multinomial masses define the law and split along the first category.
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

theorem pmf_of_invalid (n : ℕ) (ws cs : List ℕ)
    (h : ¬(cs.length = ws.length ∧ cs.sum = n)) : pmf n ws cs = 0 := ite_eq_right h

theorem dirac_singleton (a b : List ℕ) :
    (Measure.dirac a : Measure (List ℕ)) {b} =
      ((if b = a then 1 else 0 : ℝ≥0) : ℝ≥0∞) := by
  by_cases h : b = a <;> simp [h]

def rawLaw (n : ℕ) (ws : List ℕ) : Measure (List ℕ) :=
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

theorem binomial_singleton (n w t k : ℕ) (ht : 0 < w + t) :
    Binomial.law (Urn.bias w t) n {k} = (binomialPmf n w t k : ℝ≥0∞) := by
  have hd : (w : ℝ≥0) + t ≠ 0 := by exact_mod_cast ht.ne'
  rw [Binomial.law_singleton, Urn.pmf_true w t ht, Urn.pmf_false w t ht]
  simp only [binomialPmf, ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_div hd,
    ENNReal.coe_natCast, ENNReal.coe_add, Nat.cast_add]

/-- The multinomial coefficient and weight monomial split at the first category. -/
theorem pmf_cons (n w k : ℕ) (ws cs : List ℕ) (ht : 0 < w + ws.sum)
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

theorem pmf_full (n w : ℕ) (ws cs : List ℕ) (hw : 0 < w) (hz : ws.sum = 0) :
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

end

end SampLib.Multinomial
