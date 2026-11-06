import SampLib.Core.ListEncoding
import Samplers.General.DataModels

/-! Exact deterministic splitting of encoded lists. -/

open ProbLang

namespace SampLib.ListPartition

theorem splitAt_lc {rT : Type _} : (Occil.General.splitAt : Exp rT).IsLocallyClosed := by
  is_lc

theorem splitAt_fv {rT : Type _} : (Occil.General.splitAt : Exp rT).fv = ∅ := by
  simp [Occil.General.splitAt, Exp.fv]

@[simp] theorem splitAt_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.General.splitAt = Occil.General.splitAt :=
  (Exp.open_lc k e _ splitAt_lc).symm

@[simp] theorem splitAt_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.General.splitAt : Exp rT) = Occil.General.splitAt :=
  Exp.closeRec_fresh x _ k (by simp [splitAt_fv])

private theorem encode_split {rT : Type _} [ProbLangℝ rT] {α : Type _}
    (encode : α → Val rT) (x : α) (pre suffix : List α) :
    pl((inr(({(encode x).fst}, {Exp.ofVal (listVal encode pre)})),
      {Exp.ofVal (listVal encode suffix)})) =
      Exp.ofVal (.pair (listVal encode (x :: pre)) (listVal encode suffix)) := by
  simp [Exp.ofVal, listVal]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF] {α : Type _}
local bi (IProp GF)

/-- Split an arbitrary encoded list at the length of its specified prefix. -/
theorem twp_splitAt (E : CoPset) (encode : α → Val rT) (pre suffix : List α) :
    ⊢ tglWp E pl(&Occil.General.splitAt &(listVal encode (pre ++ suffix)).fst
        #int (pre.length : ℤ))
      (fun v : Val rT => iprop(⌜v = .pair (listVal encode pre) (listVal encode suffix)⌝)) := by
  induction pre with
  | nil =>
    simp only [List.nil_append, List.length_nil]
    twp_pures
    change ⊢ tglWp E (Exp.ofVal (.pair (listVal encode []) (listVal encode suffix))) _
    iapply (tglWp_value (v := .pair (listVal encode []) (listVal encode suffix)))
    itrivial
  | cons x pre IH =>
    simp only [List.cons_append, List.length_cons, listVal]
    iterate 10 twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    twp_pure
    twp_bind pl(&Occil.General.splitAt &(listVal encode (pre ++ suffix)).fst
      #int (pre.length : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply IH
    iintro %v %hv
    subst v
    twp_pures
    rw [encode_split]
    iapply (tglWp_value (v := .pair (listVal encode (x :: pre)) (listVal encode suffix)))
    ipureintro
    exact Val.ext rfl

end specification

end SampLib.ListPartition
