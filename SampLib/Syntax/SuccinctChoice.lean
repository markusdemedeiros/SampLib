import SampLib.CurriedStep
import SampLib.Syntax.ClosedExp
import SampLib.Syntax.ListAccess
import SampLib.WeightedValidation
import SampLib.GeneralSyntax
import SampLib.WeightedIntegerPower
import SampLib.Samplers.RationalCoin
import Samplers.Weighted.Rejection

/-! # Closed source routines for packed-weight rejection -/

open ProbLang

namespace SampLib.SuccinctChoice.Program

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

open scoped SampLib.SuccinctChoice.Program

private theorem weights_fv {rT : Type} [ProbLangℝ rT] (ws : List ℕ) :
    ((listVal (fun n : ℕ => Val.int n) ws : Val rT).fst).fv = ∅ := by
  induction ws with
  | nil => simp [listVal, Exp.fv]
  | cons w ws ih => simp [listVal, Exp.fv, ih]

@[simp] theorem weights_closeRec {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (k : ℕ) (x : Var) :
    Exp.closeRec k x (listVal (fun n : ℕ => Val.int n) ws : Val rT).fst =
      (listVal (fun n : ℕ => Val.int n) ws).fst :=
  Exp.closeRec_fresh x _ k (by simp [weights_fv])

private def rawMaximum {rT : Type} : Exp rT := pl%
  rec largest xs current := case! xs
    | inl(v) => current
    | inr(p) => largest (snd(p)) (if current < fst(p) then fst(p) else current)

private abbrev maximumOpening {rT : Type} : {e : Exp rT // rawMaximum = e} := by
  refine ⟨_, by conv_lhs => simp [rawMaximum, Exp.close, Exp.closeRec]⟩

abbrev maximum {rT : Type} : Exp rT := (maximumOpening (rT := rT)).val

scoped instance maximum_closed {rT : Type} : ClosedExp (maximum : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private def rawPack {rT : Type} : Exp rT := pl%
  rec encode xs index offset bits shorts := case! xs
    | inl(v) => (bits, shorts)
    | inr(p) =>
      let weight := fst(p);
      if &Occil.Weighted.integerPower #2 #32 <= weight then fail else
        let wide := (&Occil.Weighted.integerPower #2 #20 <= weight);
        let width := (if wide then #32 else #20);
        let mask := (if wide then shorts + &Occil.Weighted.integerPower #2 index else shorts);
        encode (snd(p)) (index + #1) (offset + width)
          (bits + weight * &Occil.Weighted.integerPower #2 offset) mask

private abbrev packOpening {rT : Type} : {e : Exp rT // rawPack = e} := by
  refine ⟨_, by conv_lhs => simp [rawPack, Exp.close, Exp.closeRec, ClosedExp.closeRec]⟩

abbrev pack {rT : Type} : Exp rT := (packOpening (rT := rT)).val

scoped instance pack_closed {rT : Type} : ClosedExp (pack : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

/-- The remaining source application after choosing a field width and updated mask. -/
abbrev finishPack {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (w index offset width : ℕ)
    (bits mask : ℤ) : Exp rT :=
  pl(&pack (snd((#int (w : ℤ), &(listVal (fun n : ℕ => Val.int n) ws).fst)))
    (#int (index : ℤ) + #1) (#int (offset : ℤ) + #int (width : ℤ))
    (#int bits + #int (w : ℤ) * &Occil.Weighted.integerPower #2 #int (offset : ℤ)) #int mask)

private def rawCount {rT : Type} : Exp rT := pl%
  rec rank i value := if i = #0 then #0 else value % #2 + rank (i - #1) (value / #2)

private abbrev countOpening {rT : Type} : {e : Exp rT // rawCount = e} := by
  refine ⟨_, by conv_lhs => simp [rawCount, Exp.close, Exp.closeRec]⟩

abbrev count {rT : Type} : Exp rT := (countOpening (rT := rT)).val

scoped instance count_closed {rT : Type} : ClosedExp (count : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private def rawDense {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (bound : ℤ) : Exp rT := pl%
  rec draw v :=
    let i := &Occil.uniformInt #int (ws.length : ℤ);
    if &Occil.rationalCoin
      (&Occil.getAt &(listVal (fun n : ℕ => Val.int n) ws).fst i) #int bound
      then i else draw #()

private abbrev denseOpening {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (bound : ℤ) :
    {e : Exp rT // rawDense ws bound = e} := by
  refine ⟨_, by
    conv_lhs => simp [rawDense, Exp.close, Exp.closeRec, ClosedExp.closeRec,
      weights_closeRec]⟩

abbrev dense {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (bound : ℤ) : Exp rT :=
  (denseOpening ws bound).val

scoped instance dense_closed {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (bound : ℤ) :
    ClosedExp (dense ws bound : Exp rT) where
  lc := by is_lc
  fv := by simp [Exp.fv, weights_fv, ClosedExp.fv]

private def rawPacked {rT : Type} (size bound bits shorts : ℤ) : Exp rT := pl%
  rec draw v :=
    let i := &Occil.uniformInt #int size;
    let wideBefore := &count i #int shorts;
    let offset := #32 * wideBefore + #20 * (i - wideBefore);
    let width := (if (#int shorts / &Occil.Weighted.integerPower #2 i) % #2 = #1
      then #32 else #20);
    let weight := (#int bits / &Occil.Weighted.integerPower #2 offset) %
      &Occil.Weighted.integerPower #2 width;
    if &Occil.rationalCoin weight #int bound then i else draw #()

private abbrev packedOpening {rT : Type} (size bound bits shorts : ℤ) :
    {e : Exp rT // rawPacked size bound bits shorts = e} := by
  refine ⟨_, by
    conv_lhs => simp [rawPacked, Exp.close, Exp.closeRec, ClosedExp.closeRec]⟩

abbrev packed {rT : Type} (size bound bits shorts : ℤ) : Exp rT :=
  (packedOpening size bound bits shorts).val

scoped instance packed_closed {rT : Type} (size bound bits shorts : ℤ) :
    ClosedExp (packed size bound bits shorts : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private def sourceBody {rT : Type} : Exp rT :=
  match (Occil.WeightedVariants.succinctChoice : Exp rT) with
  | .lam (.lam body) => body
  | _ => .fail

private theorem source_eq {rT : Type} : (Occil.WeightedVariants.succinctChoice : Exp rT) =
    CurriedStep.lambdas 2 sourceBody := by kernel_rfl

private theorem source_lcb {rT : Type} : Exp.lcb 2 (sourceBody : Exp rT) = true := by
  lcb_decide

def opened {rT : Type} [ProbLangℝ rT] (ws : List ℕ) :
    {e : Exp rT // CurriedStep.opened [listVal (fun n : ℕ => Val.int n) ws, .unit]
      sourceBody = e} := by
  refine ⟨_, by
    conv_lhs => simp [CurriedStep.opened, sourceBody, Occil.WeightedVariants.succinctChoice,
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
      tglWp E pl(&Occil.WeightedVariants.succinctChoice
        &(listVal (fun n : ℕ => Val.int n) ws).fst #()) Φ := by
  have h := CurriedStep.twp_apply E [] [listVal (fun n : ℕ => Val.int n) ws, .unit]
    sourceBody source_lcb Φ
  rw [(opened ws).property] at h
  change tglWp E (opened ws).val Φ ⊢
    tglWp E pl(&(CurriedStep.lambdas 2 sourceBody)
      &(listVal (fun n : ℕ => Val.int n) ws).fst #()) Φ at h
  rwa [← source_eq] at h

end specification

end SampLib.SuccinctChoice.Program
