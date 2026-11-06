module

public import SampLib.Combinatorial.Laws.Choice
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section

/-! # Uniform ordered selections without replacement

A selection records a position in the remaining list at each draw. Each of the
falling-factorial many selections has the same mass, and conditioning on the first
position leaves a uniform selection from the shortened list.
-/

open scoped ENNReal

namespace SampLib.SampleWithoutReplacement

noncomputable section

/-- A sequence of positions in successively shortened lists. -/
def Selection {α : Type _} (xs : List α) : ℕ → Type _
  | 0 => Unit
  | k + 1 => (i : Fin xs.length) × Selection (xs.eraseIdx i) k

instance selectionFintype {α : Type _} (xs : List α) (k : ℕ) :
    Fintype (Selection xs k) := by
  induction k generalizing xs with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ k IH =>
    letI (i : Fin xs.length) := IH (xs.eraseIdx i)
    exact inferInstanceAs (Fintype ((i : Fin xs.length) × Selection (xs.eraseIdx i) k))

instance {α : Type _} (xs : List α) (k : ℕ) : MeasurableSpace (Selection xs k) := ⊤
instance {α : Type _} (xs : List α) (k : ℕ) :
    MeasurableSingletonClass (Selection xs k) := ⟨fun _ => trivial⟩

/-- Decode the selected positions to list entries. -/
def selected {α : Type _} (xs : List α) : (k : ℕ) → Selection xs k → List α
  | 0, _ => []
  | k + 1, ⟨i, t⟩ => xs.get i :: selected (xs.eraseIdx i) k t

theorem selection_card {α : Type _} (xs : List α) (k : ℕ) :
    Fintype.card (Selection xs k) = xs.length.descFactorial k := by
  induction k generalizing xs with
  | zero => exact Fintype.card_unit
  | succ k IH =>
    change Fintype.card ((i : Fin xs.length) × Selection (xs.eraseIdx i) k) = _
    simp only [Fintype.card_sigma, IH, List.length_eraseIdx_of_lt (Fin.isLt _)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    cases xs.length with
    | zero => simp
    | succ n => simp only [Nat.succ_sub_one, Nat.succ_descFactorial_succ, Nat.cast_id]

theorem selection_nonempty {α : Type _} (xs : List α) (k : ℕ)
    (hk : k ≤ xs.length) : Nonempty (Selection xs k) := by
  rw [← Fintype.card_pos_iff, selection_card]
  exact Nat.descFactorial_pos.mpr hk

section distribution

open MeasureTheory Measure Finset

/-- Every ordered selection has the same probability. -/
def law {α : Type _} (xs : List α) (k : ℕ) : Measure (Selection xs k) :=
  uniformOfFinset univ

instance {α : Type _} (xs : List α) (k : ℕ) [Fact (k ≤ xs.length)] :
    IsProbabilityMeasure (law xs k) := by
  let := selection_nonempty xs k Fact.out
  exact isProbabilityMeasure_uniformOfFinset univ_nonempty

/-- Uniformity gives the reciprocal falling-factorial mass of each selection. -/
theorem law_singleton {α : Type _} (xs : List α) (k : ℕ) (t : Selection xs k) :
    law xs k {t} = (xs.length.descFactorial k : ℝ≥0∞)⁻¹ := by
  simp [law, uniformOfFinset_apply_singleton, selection_card]

theorem zero_expectation {α : Type _} (xs : List α) (F : Selection xs 0 → ℝ≥0∞) :
    ∫⁻ t, F t ∂law xs 0 = F () := by
  simp only [law, uniformOfFinset,
    lintegral_finsetSum_measure, lintegral_dirac,
    Finset.card_univ, selection_card,
    Nat.descFactorial_zero, Nat.cast_one, inv_one, one_smul]
  change (∑ t : Unit, F t) = F ()
  let : Unique (Selection xs 0) := inferInstanceAs (Unique Unit)
  exact Fintype.sum_unique F

/-- Partition ordered selections by their first chosen position. -/
theorem expectation {α : Type _} (xs : List α) (k : ℕ)
    (F : Selection xs (k + 1) → ℝ≥0∞) :
    ∫⁻ t, F t ∂law xs (k + 1) =
      (∑ i : Fin xs.length, ∫⁻ t, F ⟨i, t⟩ ∂law (xs.eraseIdx i) k) / xs.length := by
  simp only [law, uniformOfFinset, lintegral_finsetSum_measure,
    lintegral_smul_measure, lintegral_dirac, smul_eq_mul, card_univ, selection_card]
  simp_rw [List.length_eraseIdx_of_lt (Fin.isLt _)]
  have hf (n : ℕ) : n.descFactorial (k + 1) = n * (n - 1).descFactorial k := by
    cases n with
    | zero => simp
    | succ n => exact Nat.succ_descFactorial_succ n k
  rw [hf]
  simp only [Nat.cast_mul, ← Finset.mul_sum]
  change (((xs.length : ℝ≥0∞) * ((xs.length - 1).descFactorial k : ℝ≥0∞))⁻¹ *
    ∑ t : Selection xs (k + 1), F t) = _
  rw [show (∑ t : Selection xs (k + 1), F t) =
    ∑ i : Fin xs.length, ∑ t : Selection (xs.eraseIdx i) k, F ⟨i, t⟩ from
      Fintype.sum_sigma F]
  rw [ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp))]
  simp only [ENNReal.div_eq_inv_mul]
  ring

/-- Credit for the tail after a uniformly chosen first position. -/
def rankCredit {α : Type _} (xs : List α) [NeZero xs.length] (k : ℕ)
    (F : Selection xs (k + 1) → ℝ≥0∞) (j : ℕ) : ℝ≥0∞ :=
  let i := Choice.position xs.length j
  ∫⁻ t, F ⟨i, t⟩ ∂law (xs.eraseIdx i) k

theorem rank_expectation {α : Type _} (xs : List α) [NeZero xs.length]
    (k : ℕ) (F : Selection xs (k + 1) → ℝ≥0∞) :
    (∑ j ∈ Finset.range xs.length, rankCredit xs k F j) / xs.length =
      ∫⁻ t, F t ∂law xs (k + 1) := by
  rw [← Fin.sum_univ_eq_sum_range (rankCredit xs k F) xs.length, expectation]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [rankCredit]
  rw [Choice.position_of_lt i.val i.isLt]

theorem rankCredit_of_lt {α : Type _} (xs : List α) [NeZero xs.length]
    (k : ℕ) (F : Selection xs (k + 1) → ℝ≥0∞) (j : ℕ) (hj : j < xs.length) :
    rankCredit xs k F j = ∫⁻ t, F ⟨⟨j, hj⟩, t⟩ ∂law (xs.eraseIdx j) k := by
  dsimp only [rankCredit]
  rw [Choice.position_of_lt j hj]

end distribution

end

end SampLib.SampleWithoutReplacement
