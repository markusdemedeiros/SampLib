import SampLib.Core.CurriedStep
import SampLib.Core.Syntax.ClosedExp
import SampLib.Core.Syntax.ListAccess
import SampLib.Common.WeightedValidation
import SampLib.Core.GeneralSyntax
import SampLib.Weighted.Support.WeightedIntegerPower
import SampLib.Uniform.RationalCoin
import Samplers.Weighted.Rejection
import SampLib.Uniform.RndIntRange

/-! # Closed source routines for sorted dyadic rejection -/

open ProbLang

namespace SampLib.SortedChoice.Program

scoped instance power_closed {rT : Type} :
    ClosedExp (Occil.Weighted.integerPower : Exp rT) where
  lc := WeightedIntegerPower.integerPower_lc
  fv := WeightedIntegerPower.integerPower_fv

scoped instance uniform_closed {rT : Type} : ClosedExp (Occil.uniformInt : Exp rT) where
  lc := UniformInt.uniformInt_lc
  fv := UniformInt.uniformInt_fv

scoped instance coin_closed {rT : Type} : ClosedExp (Occil.rationalCoin : Exp rT) where
  lc := RationalCoin.rationalCoin_lc
  fv := RationalCoin.rationalCoin_fv

scoped instance getAt_closed {rT : Type} : ClosedExp (Occil.getAt : Exp rT) where
  lc := ListAccess.getAt_lc
  fv := ListAccess.getAt_fv

open scoped SampLib.SortedChoice.Program

private theorem weights_fv {rT : Type} [ProbLangℝ rT] (ws : List ℕ) :
    ((listVal (fun n : ℕ => Val.int n) ws : Val rT).fst).fv = ∅ := by
  induction ws with
  | nil => simp [listVal, Exp.fv]
  | cons w ws ih => simp [listVal, Exp.fv, ih]

@[simp] theorem weights_closeRec {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (k : ℕ) (x : Var) :
    Exp.closeRec k x (listVal (fun n : ℕ => Val.int n) ws : Val rT).fst =
      (listVal (fun n : ℕ => Val.int n) ws).fst :=
  Exp.closeRec_fresh x _ k (by simp [weights_fv])

scoped instance range_closed {rT : Type} : ClosedExp (Occil.rndIntRange : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

scoped instance fldr_closed {rT : Type} :
    ClosedExp (Occil.Weighted.fastLoadedDiceRoller : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private def rawCheck {rT : Type} (asc : Bool) : Exp rT := pl%
  rec monotone xs := case! xs
    | inl(v) => #true
    | inr(p) => case! (snd(p))
      | inl(v) => #true
      | inr(q) =>
        if #bool asc then
          if fst(q) < fst(p) then #false else monotone (snd(p))
        else if fst(p) < fst(q) then #false else monotone (snd(p))

private abbrev checkOpening {rT : Type} (asc : Bool) : {e : Exp rT // rawCheck asc = e} := by
  refine ⟨_, by conv_lhs => simp [rawCheck, Exp.close, Exp.closeRec]⟩

abbrev check {rT : Type} (asc : Bool) : Exp rT := (checkOpening asc).val

scoped instance check_closed {rT : Type} (asc : Bool) : ClosedExp (check asc : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private def rawGroups {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (asc : Bool) : Exp rT := pl%
  rec build lower := if #int (ws.length : ℤ) < lower then inl(#()) else
    let upper := (if #int (ws.length : ℤ) < #2 * lower - #1
      then #int (ws.length : ℤ) else #2 * lower - #1);
    let pivot := (if #bool asc then #int (ws.length : ℤ) - lower else lower - #1);
    let envelope := &Occil.getAt &(listVal (fun n : ℕ => Val.int n) ws).fst pivot;
    inr(((upper - lower + #1) * envelope, build (#2 * lower)))

private abbrev groupsOpening {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (asc : Bool) :
    {e : Exp rT // rawGroups ws asc = e} := by
  refine ⟨_, by conv_lhs =>
    simp [rawGroups, Exp.close, Exp.closeRec, ClosedExp.closeRec, weights_closeRec]⟩

abbrev groups {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (asc : Bool) : Exp rT :=
  (groupsOpening ws asc).val

scoped instance groups_closed {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (asc : Bool) :
    ClosedExp (groups ws asc : Exp rT) where
  lc := by is_lc
  fv := by simp [Exp.fv, weights_fv, ClosedExp.fv]

private def rawLoop {rT : Type} [ProbLangℝ rT] (ws envelopes : List ℕ) (asc : Bool) : Exp rT := pl%
  rec draw v :=
    let k := &Occil.Weighted.fastLoadedDiceRoller
      &(listVal (fun n : ℕ => Val.int n) envelopes).fst #();
    let lower := &Occil.Weighted.integerPower #2 k;
    let upper := (if #int (ws.length : ℤ) < #2 * lower - #1
      then #int (ws.length : ℤ) else #2 * lower - #1);
    let offset := &Occil.rndIntRange lower upper - #1;
    let index := (if #bool asc then #int (ws.length : ℤ) - #1 - offset else offset);
    let pivot := (if #bool asc then #int (ws.length : ℤ) - lower else lower - #1);
    if &Occil.rationalCoin (&Occil.getAt &(listVal (fun n : ℕ => Val.int n) ws).fst index)
      (&Occil.getAt &(listVal (fun n : ℕ => Val.int n) ws).fst pivot)
      then index else draw #()

private abbrev loopOpening {rT : Type} [ProbLangℝ rT] (ws envelopes : List ℕ) (asc : Bool) :
    {e : Exp rT // rawLoop ws envelopes asc = e} := by
  refine ⟨_, by conv_lhs =>
    simp [rawLoop, Exp.close, Exp.closeRec, ClosedExp.closeRec, weights_closeRec]⟩

abbrev loop {rT : Type} [ProbLangℝ rT] (ws envelopes : List ℕ) (asc : Bool) : Exp rT :=
  (loopOpening ws envelopes asc).val

scoped instance loop_closed {rT : Type} [ProbLangℝ rT] (ws envelopes : List ℕ) (asc : Bool) :
    ClosedExp (loop ws envelopes asc : Exp rT) where
  lc := by is_lc
  fv := by simp [Exp.fv, weights_fv, ClosedExp.fv]

private def sourceBody {rT : Type} : Exp rT :=
  match (Occil.WeightedVariants.sortedChoice : Exp rT) with
  | .lam (.lam body) => body
  | _ => .fail

private theorem source_eq {rT : Type} : (Occil.WeightedVariants.sortedChoice : Exp rT) =
    CurriedStep.lambdas 2 sourceBody := by kernel_rfl

private theorem source_lcb {rT : Type} : Exp.lcb 2 (sourceBody : Exp rT) = true := by
  lcb_decide

def opened {rT : Type} [ProbLangℝ rT] (ws : List ℕ) :
    {e : Exp rT // CurriedStep.opened [listVal (fun n : ℕ => Val.int n) ws, .unit]
      sourceBody = e} := by
  refine ⟨_, by
    conv_lhs => simp [CurriedStep.opened, sourceBody, Occil.WeightedVariants.sortedChoice,
      Exp.openRec, Exp.close, Exp.closeRec, Var.internal.injEq, openRec_val_fst,
      WeightedValidation.validWeights_openRec, WeightedValidation.validWeights_closeRec,
      WeightedValidation.sumInts_openRec, WeightedValidation.sumInts_closeRec,
      GeneralSyntax.length_openRec, GeneralSyntax.length_closeRec,
      ClosedExp.openRec,
      ClosedExp.closeRec, weights_closeRec]⟩

section specification

open Iris Iris.BI TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

/-- Open the actual source parameters using checked beta reduction. -/
theorem twp_open (E : CoPset) (ws : List ℕ) (Φ : Val rT → IProp GF) :
    tglWp E (opened ws).val Φ ⊢
      tglWp E pl(&Occil.WeightedVariants.sortedChoice
        &(listVal (fun n : ℕ => Val.int n) ws).fst #()) Φ := by
  have h := CurriedStep.twp_apply E [] [listVal (fun n : ℕ => Val.int n) ws, .unit]
    sourceBody source_lcb Φ
  rw [(opened ws).property] at h
  change tglWp E (opened ws).val Φ ⊢
    tglWp E pl(&(CurriedStep.lambdas 2 sourceBody)
      &(listVal (fun n : ℕ => Val.int n) ws).fst #()) Φ at h
  rwa [← source_eq] at h

end specification

end SampLib.SortedChoice.Program
