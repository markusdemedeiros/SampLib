import SampLib.Combinatorial.Choice
import Samplers.Combinatorial.Basic
import Metrology.Iris.LocalBI

/-! # Uniform ordered sampling without replacement

A selection records a position in the remaining list at each draw. These records
are in bijection with ordered selections of distinct original positions. They
remain distinct when the corresponding list entries happen to coincide.
-/

open ProbLang
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

private theorem selection_nonempty {α : Type _} (xs : List α) (k : ℕ)
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

private theorem zero_expectation {α : Type _} (xs : List α) (F : Selection xs 0 → ℝ≥0∞) :
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

private theorem rank_expectation {α : Type _} (xs : List α) [NeZero xs.length]
    (k : ℕ) (F : Selection xs (k + 1) → ℝ≥0∞) :
    (∑ j ∈ Finset.range xs.length, rankCredit xs k F j) / xs.length =
      ∫⁻ t, F t ∂law xs (k + 1) := by
  rw [← Fin.sum_univ_eq_sum_range (rankCredit xs k F) xs.length, expectation]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [rankCredit]
  rw [Choice.position_of_lt i.val i.isLt]

private theorem rankCredit_of_lt {α : Type _} (xs : List α) [NeZero xs.length]
    (k : ℕ) (F : Selection xs (k + 1) → ℝ≥0∞) (j : ℕ) (hj : j < xs.length) :
    rankCredit xs k F j = ∫⁻ t, F ⟨⟨j, hj⟩, t⟩ ∂law (xs.eraseIdx j) k := by
  dsimp only [rankCredit]
  rw [Choice.position_of_lt j hj]

end distribution

private theorem length_lc {rT : Type _} : (Occil.length : Exp rT).IsLocallyClosed := by is_lc
private theorem removeAt_lc {rT : Type _} : (Occil.removeAt : Exp rT).IsLocallyClosed := by is_lc

@[local simp] private theorem length_openRec {rT : Type _} (n : ℕ) (e : Exp rT) :
    Exp.openRec n e Occil.length = Occil.length := (Exp.open_lc n e _ length_lc).symm
@[local simp] private theorem removeAt_openRec {rT : Type _} (n : ℕ) (e : Exp rT) :
    Exp.openRec n e Occil.removeAt = Occil.removeAt := (Exp.open_lc n e _ removeAt_lc).symm
@[local simp] private theorem length_closeRec {rT : Type _} (n : ℕ) (x : Var) :
    Exp.closeRec n x (Occil.length : Exp rT) = Occil.length :=
  Exp.closeRec_fresh x _ n (by simp [Occil.length, Exp.fv])
@[local simp] private theorem removeAt_closeRec {rT : Type _} (n : ℕ) (x : Var) :
    Exp.closeRec n x (Occil.removeAt : Exp rT) = Occil.removeAt :=
  Exp.closeRec_fresh x _ n (by simp [Occil.removeAt, Exp.fv])

private theorem encode_cons {rT : Type _} [ProbLangℝ rT] {α : Type _}
    (encode : α → Val rT) (x : α) (xs : List α) :
    pl(inr(({(encode x).fst}, {Exp.ofVal (listVal encode xs)}))) =
      Exp.ofVal (listVal encode (x :: xs)) := by
  simp [Exp.ofVal, listVal]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF] {α : Type _}
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
/-- Removal returns the selected entry and preserves the order of all others. -/
theorem twp_removeAt (E : CoPset) (encode : α → Val rT) (xs : List α)
    (i : Fin xs.length) :
    ⊢ tglWp E pl(&Occil.removeAt &(listVal encode xs).fst #int (i.val : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.pair (encode (xs.get i))
        (listVal encode (xs.eraseIdx i))⌝)) := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons x xs IH =>
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [listVal]
      twp_pures
      change ⊢ tglWp E (Exp.ofVal (Val.pair (encode x) (listVal encode xs))) _
      iapply (tglWp_value (v := Val.pair (encode x) (listVal encode xs)))
      itrivial
    · simp only [listVal]
      twp_pure
      twp_pure
      twp_pure
      twp_pure
      twp_pure
      twp_pure
      twp_pure
      twp_pure
      twp_pure
      rw [Fin.val_succ, Nat.cast_add_one, add_sub_cancel_right]
      twp_bind pl(&Occil.removeAt &(listVal encode xs).fst #int (i.val : ℤ))
      iapply tglWp_wand
      isplitl []
      · iapply IH i
      iintro %v %hv
      subst v
      twp_pures
      change ⊢ tglWp E (Exp.ofVal (Val.pair (encode (xs.get i))
        (listVal encode (x :: xs.eraseIdx i)))) _
      iapply (tglWp_value (v := Val.pair (encode (xs.get i))
        (listVal encode (x :: xs.eraseIdx i))))
      ipureintro
      simp [List.eraseIdx, listVal]

private theorem valid_test (xs : List α) (k : ℕ) (hk : k ≤ xs.length) :
    Bool.or false (decide ((xs.length : ℤ) < k)) = false := by
  simp only [Bool.false_or, decide_eq_false_iff_not]
  omega

private theorem remaining_bound (xs : List α) (k : ℕ) (hk : k + 1 ≤ xs.length)
    (j : ℕ) (hj : j < xs.length) : k ≤ (xs.eraseIdx j).length := by
  rw [List.length_eraseIdx_of_lt hj]
  omega

/-- Uniform ordered selections, encoded by the corresponding input entries. -/
theorem twp_sampleWithoutReplacement (E : CoPset) (encode : α → Val rT)
    (xs : List α) (k : ℕ) (hk : k ≤ xs.length)
    (F : Selection xs k → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ t, F t ∂law xs k) -∗
      tglWp E pl(&Occil.sampleWithoutReplacement &(listVal encode xs).fst #int (k : ℤ))
        (fun v : Val rT => iprop(∃ t : Selection xs k,
          ⌜v = listVal encode (selected xs k t)⌝ ∗ ↯ (F t))) := by
  induction k generalizing xs with
  | zero =>
    iintro Hcredit
    twp_pure
    twp_pure
    twp_pure
    simp only [length_closeRec, length_openRec, removeAt_closeRec, removeAt_openRec,
      UniformInt.uniformInt_closeRec, UniformInt.uniformInt_openRec]
    twp_bind pl(&Occil.length &(listVal encode xs).fst)
    iapply tglWp_wand
    isplitl []
    · iapply twp_length E encode xs
    iintro %v %hv
    subst v
    twp_pures
    twp_value
    imodintro
    iexists ()
    isimp only [zero_expectation] at Hcredit
    iframe Hcredit
    ipureintro
    rfl
  | succ k IH =>
    iintro Hcredit
    twp_pure
    twp_pure
    twp_pure
    simp only [length_closeRec, length_openRec, removeAt_closeRec, removeAt_openRec,
      UniformInt.uniformInt_closeRec, UniformInt.uniformInt_openRec]
    twp_bind pl(&Occil.length &(listVal encode xs).fst)
    iapply tglWp_wand
    isplitl []
    · iapply twp_length E encode xs
    iintro %v %hv
    subst v
    twp_pures
    rw [valid_test xs (k + 1) hk]
    twp_pure
    twp_pure
    twp_pure
    twp_bind pl(&Occil.length &(listVal encode xs).fst)
    iapply tglWp_wand
    isplitl []
    · iapply twp_length E encode xs
    iintro %v %hv
    subst v
    let : NeZero xs.length := ⟨by omega⟩
    twp_bind pl(&Occil.uniformInt #int (xs.length : ℤ))
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply (UniformInt.twp_uniformInt E xs.length (NeZero.pos xs.length)
        (rankCredit xs k F))
      rw [rank_expectation]
      iexact Hcredit
    iintro %v ⟨%j, %hv, %hj, Hcredit⟩
    subst v
    twp_bind pl(&Occil.removeAt &(listVal encode xs).fst #int (j : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply twp_removeAt E encode xs ⟨j, hj⟩
    iintro %v %hv
    subst v
    twp_pure
    twp_pure
    twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    twp_bind pl(&Occil.sampleWithoutReplacement
      &(listVal encode (xs.eraseIdx j)).fst #int (k : ℤ))
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply (IH (xs.eraseIdx j) (remaining_bound xs k hk j hj)
        (fun t => F ⟨⟨j, hj⟩, t⟩))
      isimp only [rankCredit_of_lt xs k F j hj] at Hcredit
      iexact Hcredit
    iintro %v ⟨%t, %hv, Hcredit⟩
    subst v
    twp_pures
    rw [encode_cons]
    iapply (tglWp_value (v := listVal encode
      (xs.get ⟨j, hj⟩ :: selected (xs.eraseIdx j) k t)))
    iexists ⟨⟨j, hj⟩, t⟩
    iframe Hcredit
    ipureintro
    rfl

/-- The full valid domain, including zero draws from an empty list. -/
theorem sampleWithoutReplacement_distSpec (E : CoPset) (encode : α → Val rT)
    (xs : List α) (k : ℕ) (hk : k ≤ xs.length) :
    letI : Fact (k ≤ xs.length) := ⟨hk⟩
    IsDistSpec (GF := GF) E
      pl(&Occil.sampleWithoutReplacement &(listVal encode xs).fst #int (k : ℤ))
      (law xs k) (fun t => listVal encode (selected xs k t)) := by
  let : Fact (k ≤ xs.length) := ⟨hk⟩
  exact ⟨fun F _ => wand_entails (twp_sampleWithoutReplacement E encode xs k hk F)⟩

end specification

end

end SampLib.SampleWithoutReplacement
