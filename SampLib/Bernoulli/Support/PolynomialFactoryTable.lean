import SampLib.Bernoulli.Support.PolynomialFactoryCheck
import SampLib.Bernoulli.BernsteinFactory
import SampLib.Common.Laws.BernoulliMixture

/-! # Polynomial factory coefficient tables

Rational coefficient tables and their polynomial law.
-/

open Set ProbLang
open scoped unitInterval ENNReal

namespace SampLib.PolynomialFactory

open FactoryFractions

/-- Every entry produced by conversion is reduced to the source's canonical pair. -/
def table (xs : List Fraction) (n : ℕ) : List Fraction :=
  List.ofFn (fun k : Fin (n + 1) => Fraction.ofRat (coefficient xs n k))

@[simp] theorem length_table (xs : List Fraction) (n : ℕ) : (table xs n).length = n + 1 := by
  simp [table]

theorem valid_table (xs : List Fraction) (n : ℕ) :
    valid (table xs n) = true ↔ ∀ k ≤ n, coefficient xs n k ∈ Icc 0 1 := by
  rw [valid_iff]
  simp only [table, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff,
    Fraction.value_ofRat]
  constructor
  · intro h k hk
    exact h ⟨k, by omega⟩
  · intro h k
    exact h k (by omega)

/-- A rejected degree precedes every later admissible search bound. -/
theorem search_progress (xs : List Fraction) (n N : ℕ) (hn : n ≤ N)
    (hN : Admissible xs N) (h : valid (table xs n) ≠ true) : n < N := by
  apply lt_of_le_of_ne hn
  intro heq
  subst n
  exact h ((valid_table xs N).mpr hN.2)

/-- A converted coefficient equipped with the exact integer bounds. -/
def probabilityEntry (xs : List Fraction) (n : ℕ) (h : Admissible xs n)
    (k : Fin (n + 1)) : BernsteinFactory.Coefficient :=
  let q := coefficient xs n k
  have hq := (valid_fraction (Fraction.ofRat q)).mpr (by simpa using h.2 k (by omega))
  ⟨(q.num, q.den), hq.1, by change (0 : ℤ) < (q.den : ℤ); exact_mod_cast q.den_pos, hq.2⟩

/-- The same table, equipped with the proof required by the Bernstein sampler. -/
def probabilityTable (xs : List Fraction) (n : ℕ) (h : Admissible xs n) :
    List BernsteinFactory.Coefficient := List.ofFn (probabilityEntry xs n h)

@[simp] theorem length_probabilityTable (xs : List Fraction) (n : ℕ) (h : Admissible xs n) :
    (probabilityTable xs n h).length = n + 1 := by simp [probabilityTable]

theorem probabilityTable_bias (xs : List Fraction) (n k : ℕ) (h : Admissible xs n)
    (hk : k ≤ n) :
    (BernsteinFactory.coefficientBias
      (BernsteinFactory.coefficient (probabilityTable xs n h) k) : ℝ) =
      (coefficient xs n k : ℝ) := by
  rw [BernsteinFactory.coefficient, probabilityTable, List.getElem?_ofFn,
    dite_eq_left (show k < n + 1 by omega)]
  simp [probabilityEntry, BernsteinFactory.coefficientBias, RationalCoin.bias, Rat.cast_def]

private theorem listVal_ofFn {rT : Type _} [ProbLangℝ rT] {α β : Type _}
    (ea : α → Val rT) (eb : β → Val rT) (n : ℕ)
    (f : Fin n → α) (g : Fin n → β) (h : ∀ i, ea (f i) = eb (g i)) :
    listVal ea (List.ofFn f) = listVal eb (List.ofFn g) := by
  induction n with
  | zero => simp [listVal]
  | succ n IH =>
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [listVal]
    rw [h 0, IH (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ)]

theorem encoding_table {rT : Type _} [ProbLangℝ rT]
    (xs : List Fraction) (n : ℕ) (h : Admissible xs n) :
    (listVal Fraction.encode (table xs n) : Val rT) =
      listVal BernsteinFactory.encodeCoefficient (probabilityTable xs n h) := by
  apply listVal_ofFn
  intro k
  rfl

open MeasureTheory

/-- Every admissible degree gives the same Bernoulli law, independent of the search. -/
theorem probabilityTable_law (xs : List Fraction) (hxs : xs ≠ [])
    (H : ∃ n, Admissible xs n) (n : ℕ) (h : Admissible xs n) (p : unitInterval) :
    BernsteinFactory.law p (probabilityTable xs n h) = RealCoin.law (bias xs hxs H p) := by
  apply BernoulliMixture.eq_bernoulli_of_apply_true
  rw [BernsteinFactory.success_probability]
  simp only [length_probabilityTable, Nat.add_sub_cancel]
  have he := PolynomialBernstein.evaluation
    (fun j => ((input xs j).value : ℝ)) (degree xs) n h.1 p
  simp_rw [← cast_coefficient xs hxs] at he
  calc
    _ = ∑ k ∈ Finset.range (n + 1),
        ENNReal.ofReal ((coefficient xs n k : ℝ) * bernstein n k p) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
      have hp := p.2.1
      have hq := sub_nonneg.mpr p.2.2
      rw [probabilityTable_bias xs n k h hk', ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [bernstein_apply]
      ring
    _ = ENNReal.ofReal (∑ k ∈ Finset.range (n + 1),
        (coefficient xs n k : ℝ) * bernstein n k p) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro k hk
      have hq := (h.2 k (by have := Finset.mem_range.mp hk; omega)).1
      exact mul_nonneg (by exact_mod_cast hq) bernstein_nonneg
    _ = _ := by rw [he]; rfl

end SampLib.PolynomialFactory
