import SampLib.ListEncoding
import SampLib.Distributions.Sorting
import Samplers.Continuous

/-! # Uniform order statistics

The latent output is an iid uniform vector. Its encoder selects the requested
entry of the canonical ascending sort. Equal values retain their multiplicities.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.OrderStatistic

noncomputable section

/-- A fixed number of real samples, with the usual finite product sigma-algebra. -/
abbrev Sample : ℕ → Type
  | 0 => Unit
  | n + 1 => ℝ × Sample n

instance sampleMeasurableSpace : (n : ℕ) → MeasurableSpace (Sample n)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | n + 1 => by
      letI := sampleMeasurableSpace n
      exact inferInstanceAs (MeasurableSpace (ℝ × Sample n))

instance sampleMeasurableSingletonClass (n : ℕ) : MeasurableSingletonClass (Sample n) := by
  induction n with
  | zero => dsimp [Sample, sampleMeasurableSpace]; infer_instance
  | succ n IH =>
    let := IH
    change MeasurableSingletonClass (ℝ × Sample n)
    infer_instance

def samples : (n : ℕ) → Sample n → List ℝ
  | 0, _ => []
  | n + 1, s => s.1 :: samples n s.2

def sorted (n : ℕ) (s : Sample n) : List ℝ :=
  (samples n s).insertionSort (· ≤ ·)

@[simp] theorem samples_length (n : ℕ) (s : Sample n) : (samples n s).length = n := by
  induction n with
  | zero => rfl
  | succ n IH => simp [samples, IH]

@[simp] theorem sorted_length (n : ℕ) (s : Sample n) : (sorted n s).length = n := by
  simp [sorted, List.length_insertionSort]

theorem sorted_perm (n : ℕ) (s : Sample n) : (sorted n s).Perm (samples n s) :=
  List.perm_insertionSort _ _

theorem sorted_ordered (n : ℕ) (s : Sample n) : (sorted n s).Pairwise (· ≤ ·) :=
  List.pairwise_insertionSort _ _

theorem sorted_unique (n : ℕ) (s : Sample n) (xs : List ℝ)
    (hp : xs.Perm (samples n s)) (hs : xs.Pairwise (· ≤ ·)) : xs = sorted n s :=
  (hp.trans (sorted_perm n s).symm).eq_of_pairwise' hs (sorted_ordered n s)

private abbrev rankIndex (n k : ℕ) (hk : 0 < k ∧ k ≤ n) (s : Sample n) :
    Fin (sorted n s).length := ⟨k - 1, by rw [sorted_length]; omega⟩

def selected (n k : ℕ) (hk : 0 < k ∧ k ≤ n) (s : Sample n) : ℝ :=
  (sorted n s).get (rankIndex n k hk s)

section mathematics

open MeasureTheory

/-- Independent unit-uniform draws, before sorting or selecting a rank. -/
def law : (n : ℕ) → Measure (Sample n)
  | 0 => Measure.dirac ()
  | n + 1 => LawfulProbLangℝ.unifUnit.prod (law n)

instance (n : ℕ) : IsProbabilityMeasure (law n) := by
  induction n with
  | zero => dsimp [law, sampleMeasurableSpace]; infer_instance
  | succ n IH =>
    let := IH
    dsimp only [law]
    change IsProbabilityMeasure (LawfulProbLangℝ.unifUnit.prod (law n))
    infer_instance

def credit (n : ℕ) (F : Sample (n + 1) → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ s, F (x, s) ∂law n

theorem measurable_credit (n : ℕ) (F : Sample (n + 1) → ℝ≥0∞) (hF : Measurable F) :
    Measurable (credit n F) := hF.lintegral_prod_right'

/-- Tonelli conditions the iid vector on its first coordinate. -/
theorem expectation (n : ℕ) (F : Sample (n + 1) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, credit n F x ∂LawfulProbLangℝ.unifUnit = ∫⁻ s, F s ∂law (n + 1) := by
  exact (lintegral_prod _ hF.aemeasurable).symm

end mathematics

@[pl_fold] private def build : Exp ℝ := pl%
  rec go remaining := if remaining = #0 then inl(#()) else
    let x := urand;
    &Occil.insertReal x (go (remaining - #1))

private theorem valid_test (n k : ℕ) (hk : 0 < k ∧ k ≤ n) :
    Bool.or (Bool.or (decide ((n : ℤ) ≤ 0)) (decide ((k : ℤ) ≤ 0)))
      (decide ((n : ℤ) < k)) = false := by
  simp [show n ≠ 0 by omega, Nat.ne_of_gt hk.1, not_lt_of_ge hk.2]

private theorem insertReal_lc : (Occil.insertReal : Exp ℝ).IsLocallyClosed := by is_lc
private theorem insertReal_fv : (Occil.insertReal : Exp ℝ).fv = ∅ := by
  simp [Occil.insertReal, Exp.fv]
@[simp] private theorem insertReal_openRec (k : ℕ) (e : Exp ℝ) :
    Exp.openRec k e Occil.insertReal = Occil.insertReal :=
  (Exp.open_lc k e _ insertReal_lc).symm
@[simp] private theorem insertReal_closeRec (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.insertReal : Exp ℝ) = Occil.insertReal :=
  Exp.closeRec_fresh x _ k (by simp [insertReal_fv])

private theorem getAt_lc : (Occil.getAt : Exp ℝ).IsLocallyClosed := by is_lc
private theorem getAt_fv : (Occil.getAt : Exp ℝ).fv = ∅ := by simp [Occil.getAt, Exp.fv]
@[simp] private theorem getAt_openRec (k : ℕ) (e : Exp ℝ) :
    Exp.openRec k e Occil.getAt = Occil.getAt := (Exp.open_lc k e _ getAt_lc).symm
@[simp] private theorem getAt_closeRec (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.getAt : Exp ℝ) = Occil.getAt :=
  Exp.closeRec_fresh x _ k (by simp [getAt_fv])

private theorem pred_cast (k : ℕ) (hk : 0 < k) :
    (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) := by omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

omit [ProbLangDist.IsUniformReal ℝ] in
private theorem twp_insert (E : CoPset) (x : ℝ) (xs : List ℝ) :
    ⊢ tglWp E pl(&Occil.insertReal #real x &(listVal Val.real xs).fst)
      (fun v : Val ℝ => iprop(⌜v = listVal Val.real (xs.orderedInsert (· ≤ ·) x)⌝)) := by
  induction xs with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    ipureintro
    exact Val.ext (by simp [List.orderedInsert, listVal])
  | cons y xs IH =>
    simp only [listVal]
    twp_pures
    by_cases h : x ≤ y
    · rw [show ProbLangℝ.realLe x y = true from decide_eq_true h]
      twp_pures
      change ⊢ tglWp E (Exp.ofVal (listVal Val.real (x :: y :: xs))) _
      iapply (tglWp_value (v := listVal Val.real (x :: y :: xs)))
      ipureintro
      simp [List.orderedInsert, h, listVal]
    · rw [show ProbLangℝ.realLe x y = false from decide_eq_false h]
      twp_pure
      twp_pure
      twp_bind pl(&Occil.insertReal #real x &(listVal Val.real xs).fst)
      iapply tglWp_wand
      isplitl []
      · iapply IH
      iintro %v %hv
      subst v
      twp_pures
      change ⊢ tglWp E
        (Exp.ofVal (listVal Val.real (y :: xs.orderedInsert (· ≤ ·) x))) _
      iapply (tglWp_value (v := listVal Val.real (y :: xs.orderedInsert (· ≤ ·) x)))
      ipureintro
      simp [List.orderedInsert, h, listVal]

private theorem twp_build (E : CoPset) (n : ℕ) (F : Sample n → ℝ≥0∞)
    (hF : Measurable F) :
    ⊢ ↯ (∫⁻ s, F s ∂law n) -∗ tglWp E pl(&build #int (n : ℤ))
      (fun v : Val ℝ => iprop(∃ s : Sample n,
        ⌜v = listVal Val.real (sorted n s)⌝ ∗ ↯ (F s))) := by
  induction n with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists ()
    isimp only [law, MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    ipureintro
    exact Val.ext rfl
  | succ n IH =>
    iintro Hcredit
    twp_pures
    twp_bind pl(urand)
    iapply (twp_urand_exp (ε₂ := credit n F) (measurable_credit n F hF) ?_) $$ Hcredit
    · rw [expectation n F hF]
    iintro %x ⟨_, Hcredit⟩
    twp_pure
    twp_pure
    simp only [insertReal_openRec, insertReal_closeRec]
    rw [Nat.cast_add_one, add_sub_cancel_right]
    twp_bind pl(&build #int (n : ℤ))
    iapply tglWp_wand
    isplitl [Hcredit]
    · isimp only [credit] at Hcredit
      iapply (IH (fun s => F (x, s))
        (hF.comp (measurable_const.prodMk measurable_id))) $$ Hcredit
    iintro %v ⟨%s, %hv, Hcredit⟩
    subst v
    twp_bind pl(&Occil.insertReal #real x &(listVal Val.real (sorted n s)).fst)
    iapply tglWp_wand
    isplitl []
    · iapply (twp_insert E x (sorted n s))
    iintro %v %hv
    iapply (tglWp_value (v := v))
    iexists (x, s)
    iframe Hcredit
    ipureintro
    simpa only [sorted, samples, List.insertionSort_cons] using hv

theorem twp_orderStatistic (E : CoPset) (n k : ℕ) (hk : 0 < k ∧ k ≤ n)
    (F : Sample n → ℝ≥0∞) (hF : Measurable F) :
    ⊢ ↯ (∫⁻ s, F s ∂law n) -∗
      tglWp E pl(&Occil.orderStatistic #int (n : ℤ) #int (k : ℤ))
        (fun v : Val ℝ => iprop(∃ s : Sample n,
          ⌜v = Val.real (selected n k hk s)⌝ ∗ ↯ (F s))) := by
  iintro Hcredit
  twp_pure
  twp_pure
  twp_pures
  rw [valid_test n k hk]
  twp_pure
  twp_pure
  simp only [insertReal_openRec, insertReal_closeRec, getAt_openRec, getAt_closeRec]
  twp_pure
  rw [pred_cast k hk.1]
  twp_bind pl(&build #int (n : ℤ))
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply (twp_build E n F hF) $$ Hcredit
  iintro %v ⟨%s, %hv, Hcredit⟩
  subst v
  twp_bind pl(&Occil.getAt &(listVal Val.real (sorted n s)).fst #int ((k - 1 : ℕ) : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply (twp_getAt E Val.real (sorted n s) (rankIndex n k hk s))
  iintro %v %hv
  iapply (tglWp_value (v := v))
  iexists s
  iframe Hcredit
  ipureintro
  exact hv

/-- Any rank from one through `n`, encoded from the canonical sorted iid vector. -/
theorem orderStatistic_distSpec (E : CoPset) (n k : ℕ) (hk : 0 < k ∧ k ≤ n) :
    IsDistSpec (GF := GF) E pl(&Occil.orderStatistic #int (n : ℤ) #int (k : ℤ))
      (law n) (fun s => Val.real (selected n k hk s)) where
  spec F hF := wand_entails (twp_orderStatistic E n k hk F hF)

end specification

end

end SampLib.OrderStatistic
