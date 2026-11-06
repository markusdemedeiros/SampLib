import SampLib.Core.CurriedStep
import SampLib.Core.Syntax.ClosedExp
import SampLib.Common.WeightedValidation
import Samplers.Weighted.Trees

/-! # Closed source routines for Han–Hoshi interval refinement -/

open ProbLang

namespace SampLib.HanHoshi.Program

private theorem weights_fv {rT : Type} [ProbLangℝ rT] (ws : List ℕ) :
    ((listVal (fun n : ℕ => Val.int n) ws : Val rT).fst).fv = ∅ := by
  induction ws with
  | nil => simp [listVal, Exp.fv]
  | cons w ws ih => simp [listVal, Exp.fv, ih]

@[simp] theorem weights_closeRec {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (k : ℕ) (x : Var) :
    Exp.closeRec k x (listVal (fun n : ℕ => Val.int n) ws : Val rT).fst =
      (listVal (fun n : ℕ => Val.int n) ws).fst :=
  Exp.closeRec_fresh x _ k (by simp [weights_fv])

private def rawFind {rT : Type} (total : ℤ) : Exp rT := pl%
  rec visit xs previous value denominator label := case! xs
    | inl(v) => #(-1)
    | inr(p) =>
      let next := previous + fst(p);
      if (previous * denominator <= value * #int total) &&
          ((value + #1) * #int total <= next * denominator) then label
      else visit (snd(p)) next value denominator (label + #1)

private abbrev findOpening {rT : Type} (total : ℤ) : {e : Exp rT // rawFind total = e} := by
  refine ⟨_, by conv_lhs => simp [rawFind, Exp.close, Exp.closeRec]⟩

abbrev find {rT : Type} (total : ℤ) : Exp rT := (findOpening total).val

scoped instance find_closed {rT : Type} (total : ℤ) : ClosedExp (find total : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

open scoped SampLib.HanHoshi.Program

private def rawLoop {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (total : ℤ) : Exp rT := pl%
  rec refine value denominator :=
    let label := &(find total) &(listVal (fun n : ℕ => Val.int n) ws).fst #0 value denominator #0;
    if #0 <= label then label else
      refine (value * #2 + rand(#2, #())) (denominator * #2)

private abbrev loopOpening {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (total : ℤ) :
    {e : Exp rT // rawLoop ws total = e} := by
  refine ⟨_, by
    conv_lhs => simp [rawLoop, Exp.close, Exp.closeRec, ClosedExp.closeRec, weights_closeRec]⟩

abbrev loop {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (total : ℤ) : Exp rT :=
  (loopOpening ws total).val

scoped instance loop_closed {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (total : ℤ) :
    ClosedExp (loop ws total : Exp rT) where
  lc := by is_lc
  fv := by simp [Exp.fv, weights_fv]

/-- The unchanged continuation after an unresolved cell. -/
abbrev refine {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (total value denominator : ℤ) :
    Exp rT :=
  pl(&(loop ws total) (#int value * #2 + rand(#2, #())) (#int denominator * #2))

private def sourceBody {rT : Type} : Exp rT :=
  match (Occil.Weighted.hanHoshi : Exp rT) with
  | .lam (.lam body) => body
  | _ => .fail

private theorem source_eq {rT : Type} : (Occil.Weighted.hanHoshi : Exp rT) =
    CurriedStep.lambdas 2 sourceBody := by kernel_rfl

private theorem source_lcb {rT : Type} : Exp.lcb 2 (sourceBody : Exp rT) = true := by
  lcb_decide

def opened {rT : Type} [ProbLangℝ rT] (ws : List ℕ) :
    {e : Exp rT // CurriedStep.opened [listVal (fun n : ℕ => Val.int n) ws, .unit]
      sourceBody = e} := by
  refine ⟨_, by
    conv_lhs => simp [CurriedStep.opened, sourceBody, Occil.Weighted.hanHoshi,
      Exp.openRec, Exp.close, Exp.closeRec, Var.internal.injEq, openRec_val_fst,
      WeightedValidation.validWeights_openRec, WeightedValidation.validWeights_closeRec,
      WeightedValidation.sumInts_openRec, WeightedValidation.sumInts_closeRec, weights_closeRec]⟩

section specification

open Iris Iris.BI TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

/-- Open the actual source's two parameters using checked beta reduction. -/
theorem twp_open (E : CoPset) (ws : List ℕ) (Φ : Val rT → IProp GF) :
    tglWp E (opened ws).val Φ ⊢
      tglWp E pl(&Occil.Weighted.hanHoshi
        &(listVal (fun n : ℕ => Val.int n) ws).fst #()) Φ := by
  have h := CurriedStep.twp_apply E [] [listVal (fun n : ℕ => Val.int n) ws, .unit]
    sourceBody source_lcb Φ
  rw [(opened ws).property] at h
  change tglWp E (opened ws).val Φ ⊢
    tglWp E pl(&(CurriedStep.lambdas 2 sourceBody)
      &(listVal (fun n : ℕ => Val.int n) ws).fst #()) Φ at h
  rwa [← source_eq] at h

end specification

end SampLib.HanHoshi.Program
