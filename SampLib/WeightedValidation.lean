import SampLib.Samplers.WeightedChoice
import Samplers.Weighted.Core

/-! # Validation of nonnegative integer weights -/

open ProbLang

namespace SampLib.WeightedValidation

private def check {rT : Type _} : Exp rT := pl%
  rec visit xs := case! xs
    | inl(u) => #true
    | inr(p) => if fst(p) < #0 then #false else visit (snd(p))

theorem sumInts_lc {rT : Type _} : (Occil.sumInts : Exp rT).IsLocallyClosed := by is_lc

theorem sumInts_fv {rT : Type _} : (Occil.sumInts : Exp rT).fv = ∅ := by
  simp [Occil.sumInts, Exp.fv]

@[simp] theorem sumInts_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.sumInts = Occil.sumInts :=
  (Exp.open_lc k e _ sumInts_lc).symm

@[simp] theorem sumInts_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.sumInts : Exp rT) = Occil.sumInts :=
  Exp.closeRec_fresh x _ k (by simp [sumInts_fv])

theorem validWeights_lc {rT : Type _} :
    (Occil.Weighted.validWeights : Exp rT).IsLocallyClosed := by is_lc

theorem validWeights_fv {rT : Type _} :
    (Occil.Weighted.validWeights : Exp rT).fv = ∅ := by
  simp [Occil.Weighted.validWeights, Occil.sumInts, Exp.fv, Exp.close, Exp.closeRec]

@[simp] theorem validWeights_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.Weighted.validWeights = Occil.Weighted.validWeights :=
  (Exp.open_lc k e _ validWeights_lc).symm

@[simp] theorem validWeights_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.Weighted.validWeights : Exp rT) = Occil.Weighted.validWeights :=
  Exp.closeRec_fresh x _ k (by simp [validWeights_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_check (E : CoPset) (ws : List ℕ) :
    ⊢ tglWp E pl(&check &(listVal (fun n : ℕ => Val.int n) ws).fst)
      (fun v : Val rT => iprop(⌜v = Val.bool true⌝)) := by
  induction ws with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    itrivial
  | cons w ws ih =>
    simp only [listVal]
    iterate 8 twp_pure
    exact ih

/-- Natural weights of positive total pass validation. -/
theorem twp_validWeights (E : CoPset) (ws : List ℕ) (hs : 0 < ws.sum) :
    ⊢ tglWp E pl(&Occil.Weighted.validWeights
        &(listVal (fun n : ℕ => Val.int n) ws).fst)
      (fun v : Val rT => iprop(⌜v = Val.bool true⌝)) := by
  iterate 2 twp_pure
  twp_bind pl(&check &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_check E ws
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.sumInts &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedChoice.twp_sumInts E ws
  iintro %v %hv
  subst v
  twp_pures
  twp_value
  imodintro
  ipureintro
  apply Val.ext
  exact congrArg (fun b => (Exp.lit (.bool b) : Exp rT))
    (decide_eq_true (show (0 : ℤ) < ws.sum by exact_mod_cast hs))

end specification

end SampLib.WeightedValidation
