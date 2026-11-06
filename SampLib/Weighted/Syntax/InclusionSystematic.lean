import SampLib.Core.BetaStep
import SampLib.Core.GeneralSyntax
import SampLib.Common.WeightedValidation
import Samplers.Weighted.Reservoir

/-! # Source openings for systematic PPS sampling -/

open ProbLang

namespace SampLib.InclusionSystematic.Program

private def rawScan {rT : Type} (count total ticket : ℤ) : Exp rT := pl%
  rec select xs before label := case! xs
    | inl(u) => inl(#())
    | inr(p) =>
      let width := #int count * fst(p);
      if #int total < width then fail else
        let after := before + width;
        if (before + #int ticket) / #int total < (after + #int ticket) / #int total then
          inr((label, select (snd(p)) after (label + #1)))
        else select (snd(p)) after (label + #1)

private def scanOpening {rT : Type} (count total ticket : ℤ) :
    {e : Exp rT // rawScan count total ticket = e} := by
  refine ⟨_, by conv_lhs => simp [rawScan, Exp.close, Exp.closeRec]⟩

/-- The deterministic scan, with its quotation closures normalized once. -/
def scan {rT : Type} (count total ticket : ℤ) : Exp rT :=
  (scanOpening count total ticket).val

private def sourceBody {rT : Type} : Exp rT :=
  match (Occil.Weighted.inclusionSystematic : Exp rT) with
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
    {e : Exp rT //
      Exp.open' (Exp.openRec 1 weights.fst countBody) (.lit (.int count)) = e} := by
  refine ⟨_, by
    conv_lhs =>
      simp [countBody, sourceBody, Occil.Weighted.inclusionSystematic, Exp.open', Exp.openRec,
        Exp.close, Exp.closeRec, Var.internal.injEq, ProbLang.openRec_val_fst,
        GeneralSyntax.length_openRec, GeneralSyntax.length_closeRec,
        WeightedValidation.validWeights_openRec, WeightedValidation.validWeights_closeRec,
        WeightedValidation.sumInts_openRec, WeightedValidation.sumInts_closeRec,
        UniformInt.uniformInt_openRec, UniformInt.uniformInt_closeRec]⟩

section specification

open Iris Iris.BI ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]

/-- Open the source without expanding its closed helper programs. -/
theorem twp_open (E : CoPset) (weights : Val rT) (count : ℤ) (Φ : Val rT → IProp GF) :
    tglWp E (opened weights count).val Φ ⊢
      tglWp E pl(&Occil.Weighted.inclusionSystematic &weights.fst #int count) Φ := by
  have hfirst := twp_beta E [.appL (.int count)] (.lam countBody) weights
    (source (rT := rT)).lc Φ
  have hsecond := twp_beta E [] (Exp.openRec 1 weights.fst countBody) (.int count)
    (weightedSource weights).lc Φ
  rw [(opened weights count).property] at hsecond
  exact hsecond.trans hfirst

end specification

end SampLib.InclusionSystematic.Program
