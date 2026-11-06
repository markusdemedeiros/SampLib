import SampLib.Common.WeightedValidation
import SampLib.Core.Syntax.ListAccess
import SampLib.Core.Syntax.ListValues
import Samplers.Weighted.Choice

/-! # Categorical sampling from an expanded table

The deterministic table contains exactly one entry per unit of weight. Its
entries are the same consecutive blocks as the categorical rank partition.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.FlatChoice

noncomputable section

def table : List ℕ → ℕ → List ℕ
  | [], _ => []
  | w :: ws, offset => List.replicate w offset ++ table ws (offset + 1)

@[simp] theorem length_table (ws : List ℕ) (offset : ℕ) :
    (table ws offset).length = ws.sum := by
  induction ws generalizing offset with
  | nil => rfl
  | cons w ws ih => simp [table, ih]

/-- Table lookup is precisely the category containing the uniform rank. -/
theorem lookup (ws : List ℕ) (offset k : ℕ) (hk : k < ws.sum) :
    (table ws offset)[k]?.getD 0 = offset + WeightedChoice.category ws k := by
  induction ws generalizing offset k with
  | nil => simp at hk
  | cons w ws ih =>
    simp only [table]
    by_cases h : k < w
    · rw [List.getElem?_append_left (by simpa using h)]
      simp [h, WeightedChoice.category]
    · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt h)]
      simp only [List.length_replicate]
      rw [ih (offset + 1) (k - w) (by simp only [List.sum_cons] at hk; omega)]
      simp only [WeightedChoice.category, ite_eq_right h]
      omega

private def expand {rT : Type _} : Exp rT := pl%
  rec build xs index := case! xs
    | inl(v) => inl(#())
    | inr(p) =>
      let copies := (rec copiesOf remaining :=
        if remaining = #0 then build (snd(p)) (index + #1)
        else inr((index, copiesOf (remaining - #1))));
      copies (fst(p))

-- Insert the locally closed continuation directly, without introducing captures.
private def copies {rT : Type _} (next : Exp rT) (offset : ℕ) : Exp rT :=
  .fix (.lam (.cond (.binop .eq (.bvar 0) (.lit (.int 0))) next
    (.inr (.pair (.lit (.int offset))
      (.app (.bvar 1) (.binop .minus (.bvar 0) (.lit (.int 1))))))))

private theorem expand_lc {rT : Type _} : (expand : Exp rT).IsLocallyClosed := by is_lc

private theorem expand_fv {rT : Type _} : (expand : Exp rT).fv = ∅ := by
  simp [expand, Exp.fv]

@[local simp] private theorem expand_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e expand = expand := (Exp.open_lc k e _ expand_lc).symm

@[local simp] private theorem expand_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (expand : Exp rT) = expand :=
  Exp.closeRec_fresh x _ k (by simp [expand_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_copies (E : CoPset) (next : Exp rT) (hnext : next.IsLocallyClosed)
    (ys : List ℕ) (offset n : ℕ)
    (h : ⊢ tglWp E next (fun v => iprop(⌜v = listVal (fun i : ℕ => Val.int i) ys⌝))) :
    ⊢ tglWp E pl(&(copies next offset) #int (n : ℤ))
      (fun v => iprop(⌜v = listVal (fun i : ℕ => Val.int i)
        (List.replicate n offset ++ ys)⌝)) := by
  have hopen (k : ℕ) (e : Exp rT) : Exp.openRec k e next = next :=
    (Exp.open_lc k e next hnext).symm
  induction n with
  | zero =>
    simp only [copies]
    twp_pures
    simp only [hopen, List.replicate_zero, List.nil_append]
    exact h
  | succ n ih =>
    simp only [copies]
    iterate 5 twp_pure
    simp only [hopen, Nat.cast_add_one, add_sub_cancel_right]
    twp_bind pl(&(copies next offset) #int (n : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply ih
    iintro %v %hv
    subst v
    change ⊢ tglWp E
      (Exp.ofVal (listVal (fun i : ℕ => Val.int i)
        (offset :: (List.replicate n offset ++ ys))))
      (fun v => iprop(⌜v = listVal (fun i : ℕ => Val.int i)
        (List.replicate (n + 1) offset ++ ys)⌝))
    iapply (tglWp_value (v := listVal (rT := rT) (fun i : ℕ => Val.int i)
      (offset :: (List.replicate n offset ++ ys))))
    ipureintro
    simp [List.replicate_succ]

private theorem twp_expand (E : CoPset) (ws : List ℕ) (offset : ℕ) :
    ⊢ tglWp E pl(&expand &(listVal (fun i : ℕ => Val.int i) ws).fst #int (offset : ℤ))
      (fun v => iprop(⌜v = listVal (fun i : ℕ => Val.int i) (table ws offset)⌝)) := by
  induction ws generalizing offset with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    ipureintro
    exact Val.ext rfl
  | cons w ws ih =>
    let next : Exp rT := pl(&expand
      (snd((#int (w : ℤ), &(listVal (fun i : ℕ => Val.int i) ws).fst)))
      (#int (offset : ℤ) + #1))
    have hnext : next.IsLocallyClosed := by dsimp [next]; is_lc
    have htail : ⊢ tglWp E next (fun v =>
        iprop(⌜v = listVal (fun i : ℕ => Val.int i) (table ws (offset + 1))⌝)) := by
      dsimp [next]
      iterate 2 twp_pure
      rw [← Nat.cast_add_one]
      exact ih (offset + 1)
    have hcopies := twp_copies E next hnext (table ws (offset + 1)) offset w htail
    simp [next, copies, expand, Exp.close, Exp.closeRec] at hcopies
    simp only [listVal]
    iterate 7 twp_pure
    exact hcopies

private theorem twp_lookup (E : CoPset) (ws : List ℕ) (offset k : ℕ)
    (hk : k < ws.sum) :
    ⊢ tglWp E pl(&Occil.getAt
      &(listVal (fun i : ℕ => Val.int i) (table ws offset)).fst #int (k : ℤ))
      (fun v => iprop(⌜v = Val.int ((offset + WeightedChoice.category ws k : ℕ) : ℤ)⌝)) := by
  have hbound : k < (table ws offset).length := by simpa using hk
  have hlookup := lookup ws offset k hk
  simp only [List.getElem?_eq_getElem hbound, Option.getD_some] at hlookup
  simpa only [List.get_eq_getElem, hlookup] using
    twp_getAt E (fun i : ℕ => Val.int i) (table ws offset) ⟨k, hbound⟩

variable [ProbLangDist.IsUniformInt rT]

/-- A uniform table position has the original normalized categorical law. -/
theorem flatChoice_distSpec (E : CoPset) (ws : List ℕ) [NeZero ws.sum] :
    IsDistSpec (GF := GF) E pl(&Occil.WeightedVariants.flatChoice
      &(listVal (fun i : ℕ => Val.int i) ws).fst #())
      (WeightedChoice.law ws) (fun i : ℕ => Val.int (i : ℤ)) := by
  refine ⟨fun F _ => ?_⟩
  iintro Hcredit
  iterate 2 twp_pure
  twp_bind pl(&Occil.Weighted.validWeights &(listVal (fun i : ℕ => Val.int i) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedValidation.twp_validWeights E ws (NeZero.pos ws.sum)
  iintro %v %hv
  subst v
  iterate 2 twp_pure
  simp only [ListAccess.getAt_openRec, ListAccess.getAt_closeRec,
    WeightedValidation.sumInts_openRec, WeightedValidation.sumInts_closeRec]
  twp_bind pl(&expand &(listVal (fun i : ℕ => Val.int i) ws).fst #0)
  iapply tglWp_wand
  isplitl []
  · iapply twp_expand E ws 0
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.sumInts &(listVal (fun i : ℕ => Val.int i) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedChoice.twp_sumInts E ws
  iintro %v %hv
  subst v
  twp_bind pl(&Occil.uniformInt #int (ws.sum : ℤ))
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply UniformInt.twp_uniformInt E ws.sum (NeZero.pos ws.sum)
      (fun k => F (WeightedChoice.category ws k))
    rw [WeightedChoice.rank_partition, ← WeightedChoice.lintegral_law]
    iexact Hcredit
  iintro %v ⟨%k, %hv, %hk, Hcredit⟩
  subst v
  simp only [Exp.ofVal]
  twp_bind pl(&Occil.getAt &(listVal (fun i : ℕ => Val.int i) (table ws 0)).fst
    #int (k : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_lookup E ws 0 k hk
  iintro %v %hv
  iapply (tglWp_value (v := v))
  iexists WeightedChoice.category ws k
  iframe Hcredit
  ipureintro
  simpa only [Nat.zero_add] using hv

end specification

end

end SampLib.FlatChoice
