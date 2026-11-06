import SampLib.ListEncoding
import Samplers.General.Core

/-! Deterministic operations on encoded sampler lists. -/

open ProbLang

namespace SampLib.ListOperations

theorem append_lc {rT : Type _} : (Occil.General.append : Exp rT).IsLocallyClosed := by is_lc

theorem append_fv {rT : Type _} : (Occil.General.append : Exp rT).fv = ∅ := by
  simp [Occil.General.append, Exp.fv]

@[simp] theorem append_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.General.append = Occil.General.append :=
  (Exp.open_lc k e _ append_lc).symm

@[simp] theorem append_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.General.append : Exp rT) = Occil.General.append :=
  Exp.closeRec_fresh x _ k (by simp [append_fv])

theorem repeatSample_lc {rT : Type _} : (Occil.repeatSample : Exp rT).IsLocallyClosed := by is_lc

theorem repeatSample_fv {rT : Type _} : (Occil.repeatSample : Exp rT).fv = ∅ := by
  simp [Occil.repeatSample, Exp.fv]

@[simp] theorem repeatSample_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.repeatSample = Occil.repeatSample :=
  (Exp.open_lc k e _ repeatSample_lc).symm

@[simp] theorem repeatSample_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.repeatSample : Exp rT) = Occil.repeatSample :=
  Exp.closeRec_fresh x _ k (by simp [repeatSample_fv])

private theorem encode_cons {rT : Type _} [ProbLangℝ rT] {α : Type _}
    (encode : α → Val rT) (x : α) (xs : List α) :
    pl(inr(({(encode x).fst}, {Exp.ofVal (listVal encode xs)}))) =
      Exp.ofVal (listVal encode (x :: xs)) := by simp [Exp.ofVal, listVal]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF] {α : Type _}
local bi (IProp GF)

theorem twp_append (E : CoPset) (encode : α → Val rT) (xs ys : List α) :
    ⊢ tglWp E pl(&Occil.General.append &(listVal encode xs).fst &(listVal encode ys).fst)
      (fun v : Val rT => iprop(⌜v = listVal encode (xs ++ ys)⌝)) := by
  induction xs with
  | nil =>
    simp only [listVal]
    twp_pures
    change ⊢ tglWp E (Exp.ofVal (listVal encode ys))
      (fun v : Val rT => iprop(⌜v = listVal encode ys⌝))
    iapply (tglWp_value (v := listVal encode ys))
    itrivial
  | cons x xs IH =>
    simp only [listVal]
    iterate 6 twp_pure
    twp_bind pl(&Occil.General.append
      &(listVal encode xs).fst &(listVal encode ys).fst)
    iapply tglWp_wand
    isplitl []
    · iapply IH
    iintro %v %hv
    subst v
    twp_pure
    rw [encode_cons]
    iapply (tglWp_value (v := listVal encode (x :: (xs ++ ys))))
    itrivial

end specification

end SampLib.ListOperations
