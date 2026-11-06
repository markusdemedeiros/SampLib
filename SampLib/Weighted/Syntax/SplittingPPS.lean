import SampLib.Common.WeightedValidation
import SampLib.Core.BetaStep
import SampLib.Core.Syntax.ListAccess
import SampLib.Core.GeneralSyntax
import SampLib.Uniform.RationalCoin
import Samplers.Weighted.Reservoir

/-! # Closed source routines for Deville–Tillé splitting -/

open ProbLang

namespace SampLib.SplittingPPS

private theorem insert_lc {rT : Type} :
    (Occil.Weighted.insertProbability : Exp rT).IsLocallyClosed := by is_lc

private theorem insert_fv {rT : Type} :
    (Occil.Weighted.insertProbability : Exp rT).fv = ∅ := by
  simp [Occil.Weighted.insertProbability, Exp.fv]

@[simp] theorem insert_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.Weighted.insertProbability = Occil.Weighted.insertProbability :=
  (Exp.open_lc k e _ insert_lc).symm

@[simp] theorem insert_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.Weighted.insertProbability : Exp rT) =
      Occil.Weighted.insertProbability := Exp.closeRec_fresh x _ k (by simp [insert_fv])

namespace Program

private def rawPrepare {rT : Type} (count total : ℤ) : Exp rT := pl%
  rec build xs label := case! xs
    | inl(u) => inl(#())
    | inr(p) =>
      let numerator := #int count * fst(p);
      if #int total < numerator then fail else
        &Occil.Weighted.insertProbability (numerator, label)
          (build (snd(p)) (label + #1))

private abbrev prepareOpening {rT : Type} (count total : ℤ) :
    {e : Exp rT // rawPrepare count total = e} := by
  refine ⟨_, by
    conv_lhs => simp [rawPrepare, Exp.close, Exp.closeRec, insert_closeRec]⟩

/-- Source preprocessing with closure normalization performed outside symbolic execution. -/
abbrev prepare {rT : Type} (count total : ℤ) : Exp rT := (prepareOpening count total).val

private def rawAdjust {rT : Type} (amount : ℤ) : Exp rT := pl%
  rec update xs remaining := case! xs
    | inl(u) => inl(#())
    | inr(p) =>
      let item := fst(p);
      let numerator := (if #0 < remaining then fst(item) else fst(item) - #int amount);
      let rest := update (snd(p)) (remaining - #1);
      &Occil.Weighted.insertProbability (numerator, snd(item)) rest

private abbrev adjustOpening {rT : Type} (amount : ℤ) :
    {e : Exp rT // rawAdjust amount = e} := by
  refine ⟨_, by
    conv_lhs => simp [rawAdjust, Exp.close, Exp.closeRec, insert_closeRec]⟩

/-- Subtract from the upper block and restore the stable ordering. -/
abbrev adjust {rT : Type} (amount : ℤ) : Exp rT := (adjustOpening amount).val

/-- The source's fixed-size accepting branch. -/
abbrev select {rT : Type} : Exp rT := pl%
  rec take xs remaining := case! xs
    | inl(u) => inl(#())
    | inr(p) =>
      let item := fst(p);
      if #0 < remaining then take (snd(p)) (remaining - #1)
      else inr((snd(item), take (snd(p)) #0))

/-- Tail-result binder assembled before inserting closed data values. -/
abbrev finish {rT : Type} (amount remaining oldNumerator label numerator : ℤ)
    (items : Val rT) : Exp rT :=
  .app (.lam (.app (.app Occil.Weighted.insertProbability
    (.pair (.lit (.int numerator))
      (.snd (.pair (.lit (.int oldNumerator)) (.lit (.int label)))))) (.bvar 0)))
    (.app (.app (adjust amount) items.fst) (.lit (.int remaining)))

private theorem select_lc {rT : Type} : (select : Exp rT).IsLocallyClosed := by is_lc

@[simp] theorem select_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e select = select := (Exp.open_lc k e _ select_lc).symm

@[simp] theorem select_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (select : Exp rT) = select :=
  Exp.closeRec_fresh x _ k (by simp [Exp.fv])

private def rawLoop {rT : Type} (size count : ℤ) : Exp rT := pl%
  rec split items denominator :=
    let lowBoundary := &Occil.getAt items (#int size - #int count - #1);
    let highBoundary := &Occil.getAt items (#int size - #int count);
    let complement := denominator - fst(lowBoundary);
    let high := fst(highBoundary);
    let amount := (if complement < high then complement else high);
    if amount <= #0 then fail else
      if &Occil.rationalCoin amount denominator then &select items (#int size - #int count) else
        let update := (rec adjust xs remaining := case! xs
          | inl(u) => inl(#())
          | inr(p) =>
            let item := fst(p);
            let numerator := (if #0 < remaining then fst(item) else fst(item) - amount);
            let rest := adjust (snd(p)) (remaining - #1);
            &Occil.Weighted.insertProbability (numerator, snd(item)) rest);
        split (update items (#int size - #int count)) (denominator - amount)

private abbrev loopOpening {rT : Type} (size count : ℤ) :
    {e : Exp rT // rawLoop size count = e} := by
  refine ⟨_, by
    conv_lhs => simp [rawLoop, Exp.close, Exp.closeRec, insert_closeRec,
      ListAccess.getAt_closeRec, RationalCoin.rationalCoin_closeRec, select_closeRec]⟩

/-- One source split, retaining the original integer-index computations and update body. -/
abbrev loop {rT : Type} (size count : ℤ) : Exp rT := (loopOpening size count).val

private def sourceBody {rT : Type} : Exp rT :=
  match (Occil.Weighted.inclusionSplitting : Exp rT) with
  | .lam body => body
  | _ => .lit .unit

private def countBody {rT : Type} : Exp rT :=
  match sourceBody (rT := rT) with
  | .lam body => body
  | _ => .lit .unit

private theorem countBody_lcb {rT : Type} : Exp.lcb 2 (countBody (rT := rT)) = true := by
  lcb_decide

private def source {rT : Type} : Val rT := by
  have hc : (Exp.lam (.lam (countBody (rT := rT)))).IsLocallyClosed :=
    Exp.lcb_imp_lc (show Exp.lcb 0 (.lam (.lam (countBody (rT := rT)))) = true from
      countBody_lcb (rT := rT))
  exact ⟨.lam (.lam countBody), .lam hc, hc⟩

private def weightedSource {rT : Type} (weights : Val rT) : Val rT := by
  have hc : (Exp.lam (Exp.openRec 1 weights.fst (countBody (rT := rT)))).IsLocallyClosed :=
    Exp.lcb_imp_lc (show Exp.lcb 1 (Exp.openRec 1 weights.fst (countBody (rT := rT))) = true
      from Exp.lcb_openRec (Exp.lcb_ofVal 1 weights) (countBody_lcb (rT := rT)))
  exact ⟨.lam (Exp.openRec 1 weights.fst countBody), .lam hc, hc⟩

def opened {rT : Type} (weights : Val rT) (count : ℤ) :
    {e : Exp rT // Exp.open' (Exp.openRec 1 weights.fst countBody) (.lit (.int count)) = e} := by
  refine ⟨_, by
    conv_lhs =>
      simp [countBody, sourceBody, Occil.Weighted.inclusionSplitting, Exp.open', Exp.openRec,
        Exp.close, Exp.closeRec, Var.internal.injEq, ProbLang.openRec_val_fst,
        GeneralSyntax.length_openRec, GeneralSyntax.length_closeRec,
        WeightedValidation.validWeights_openRec, WeightedValidation.validWeights_closeRec,
        WeightedValidation.sumInts_openRec, WeightedValidation.sumInts_closeRec,
        insert_openRec, insert_closeRec, ListAccess.getAt_openRec, ListAccess.getAt_closeRec,
        RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec]⟩

section specification

open Iris Iris.BI ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]

/-- Open the two source parameters without normalizing during symbolic execution. -/
theorem twp_open (E : CoPset) (weights : Val rT) (count : ℤ) (Φ : Val rT → IProp GF) :
    tglWp E (opened weights count).val Φ ⊢
      tglWp E pl(&Occil.Weighted.inclusionSplitting &weights.fst #int count) Φ := by
  have hfirst := twp_beta E [.appL (.int count)] (.lam countBody) weights
    (source (rT := rT)).lc Φ
  have hsecond := twp_beta E [] (Exp.openRec 1 weights.fst countBody) (.int count)
    (weightedSource weights).lc Φ
  rw [(opened weights count).property] at hsecond
  exact hsecond.trans hfirst

end specification

end Program

end SampLib.SplittingPPS
