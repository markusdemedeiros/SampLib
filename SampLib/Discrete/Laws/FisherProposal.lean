import Metrology.ProbLang.Discrete
import SampLib.Discrete.Laws.BinomialBinary
import SampLib.Common.Laws.AcceptedProposal

/-! # Independent binomial proposal for multivariate Fisher sampling

Each color draws an independent binomial count with success odds `oᵢ`. The
proposal mass of a count vector is a coefficient over a common denominator.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.FisherMultivariate

noncomputable section

abbrev bias (odds : ℕ) := BinomialBinary.bias odds (odds + 1)

/-- Independent binomial counts; invalid list shapes have a harmless total extension. -/
def proposal : List ℕ → List ℕ → Measure (List ℕ)
  | [], _ => Measure.dirac []
  | _ :: _, [] => Measure.dirac []
  | c :: cs, o :: os => ((Binomial.law (bias o) c).prod (proposal cs os)).map
      (fun z => z.1 :: z.2)

instance (counts odds : List ℕ) : IsProbabilityMeasure (proposal counts odds) := by
  induction counts generalizing odds with
  | nil => dsimp [proposal]; infer_instance
  | cons c cs IH =>
    cases odds with
    | nil => dsimp [proposal]; infer_instance
    | cons o os =>
      let := IH os
      constructor
      rw [proposal, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
      simp

/-- Condition on one independent binomial component. -/
theorem proposal_cons (c o : ℕ) (cs os : List ℕ) (F : List ℕ → ℝ≥0∞) :
    ∫⁻ x, (∫⁻ xs, F (x :: xs) ∂proposal cs os) ∂Binomial.law (bias o) c =
      ∫⁻ xs, F xs ∂proposal (c :: cs) (o :: os) := by
  rw [proposal, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]

/-- Componentwise count bounds include the exact number of returned components. -/
theorem proposal_support (counts odds : List ℕ) (hlen : counts.length = odds.length) :
    ∀ᵐ xs ∂proposal counts odds, xs.length = counts.length ∧ List.Forall₂ (· ≤ ·) xs counts := by
  induction counts generalizing odds with
  | nil => simp [proposal]
  | cons c cs IH =>
    cases odds with
    | nil => simp at hlen
    | cons o os =>
      have ht : cs.length = os.length := by simpa using hlen
      rw [proposal, ae_map_iff (measurable_of_countable _).aemeasurable
        (Set.to_countable _).measurableSet]
      apply (Measure.ae_prod_iff_ae_ae (Set.to_countable _).measurableSet).2
      filter_upwards [Binomial.support (bias o) c] with x hx
      filter_upwards [IH os ht] with xs hxs
      exact ⟨by simp [hxs.1], List.Forall₂.cons hx hxs.2⟩

/-- The unnormalized Fisher coefficient, extended by zero to invalid shapes. -/
def coefficient : List ℕ → List ℕ → List ℕ → ℕ
  | [], [], [] => 1
  | c :: cs, o :: os, x :: xs => c.choose x * o ^ x * coefficient cs os xs
  | _, _, _ => 0

/-- The common denominator of the independent binomial proposal masses. -/
def denominator : List ℕ → List ℕ → ℕ
  | c :: cs, o :: os => (o + 1) ^ c * denominator cs os
  | _, _ => 1

theorem denominator_pos (counts odds : List ℕ) : 0 < denominator counts odds := by
  induction counts generalizing odds with
  | nil => simp [denominator]
  | cons c cs IH =>
    cases odds with
    | nil => simp [denominator]
    | cons o os => exact Nat.mul_pos (Nat.pow_pos (by omega)) (IH os)

private theorem bias_coe (o : ℕ) : (bias o : ℝ) = (o : ℝ) / (o + 1) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    BinomialBinary.bias_coe o (o + 1) (by omega) (by omega)

private theorem complement_coe (o : ℕ) : 1 - (bias o : ℝ) = 1 / (o + 1) := by
  rw [bias_coe]
  have h : (o : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- A single proposal count has one integer polynomial over its common denominator. -/
private theorem binomial_atom (c o x : ℕ) :
    (Binomial.law (bias o) c) {x} =
      ENNReal.ofReal (((c.choose x * o ^ x : ℕ) : ℝ) / ((o + 1) ^ c : ℕ)) := by
  rw [Binomial.law_eq_binomial, ProbabilityTheory.binomial_singleton]
  by_cases hx : x ≤ c
  · rw [complement_coe, bias_coe, div_pow, div_pow, one_pow]
    congr 1
    push_cast
    rw [mul_assoc, div_mul_div_comm, ← pow_add, Nat.add_sub_of_le hx]
    ring
  · simp [Nat.choose_eq_zero_of_lt (lt_of_not_ge hx)]

private theorem proposal_atom_cons (c o x : ℕ) (cs os xs : List ℕ) :
    (proposal (c :: cs) (o :: os)) {x :: xs} =
      (Binomial.law (bias o) c) {x} * (proposal cs os) {xs} := by
  rw [proposal, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hpre : (fun z : ℕ × List ℕ => z.1 :: z.2) ⁻¹' {x :: xs} = {(x, xs)} := by
    ext z
    rcases z with ⟨j, js⟩
    simp
  rw [hpre, ← Set.singleton_prod_singleton, Measure.prod_prod]

private theorem proposal_atom_nil (c o : ℕ) (cs os : List ℕ) :
    (proposal (c :: cs) (o :: os)) {[]} = 0 := by
  rw [proposal, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hpre : (fun z : ℕ × List ℕ => z.1 :: z.2) ⁻¹' {[]} = ∅ := by ext z; simp
  rw [hpre, measure_empty]

/-- Every proposal atom has the Fisher coefficient over a common denominator. -/
theorem proposal_singleton (counts odds xs : List ℕ) (hlen : counts.length = odds.length) :
    (proposal counts odds) {xs} =
      ENNReal.ofReal ((coefficient counts odds xs : ℝ) / denominator counts odds) := by
  induction counts generalizing odds xs with
  | nil =>
    have ho : odds = [] := List.length_eq_zero_iff.mp hlen.symm
    subst odds
    cases xs <;> simp [proposal, coefficient, denominator]
  | cons c cs IH =>
    cases odds with
    | nil => simp at hlen
    | cons o os =>
      have ht : cs.length = os.length := by simpa using hlen
      cases xs with
      | nil => simp [proposal_atom_nil, coefficient]
      | cons x xs =>
        rw [proposal_atom_cons, binomial_atom, IH os xs ht,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [coefficient, denominator, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
          Nat.cast_one, div_mul_div_comm]

end

end SampLib.FisherMultivariate
