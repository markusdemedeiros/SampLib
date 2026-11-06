import SampLib.Core.BetaStep
import SampLib.Common.WeightedValidation
import SampLib.Core.Syntax.Arrays
import SampLib.Core.ListOperations
import SampLib.Uniform.UniformInt
import Samplers.Weighted.Sequential

/-! # Opening the alias-sampling source term

These definitions peel the two outer binders off `Occil.aliasSamples` and normalize the
body once the weights and the sample count are substituted.
-/

open ProbLang

namespace SampLib.AliasSamples

def sourceBody {rT : Type} : Exp rT :=
  match (Occil.aliasSamples : Exp rT) with
  | .lam body => body
  | _ => .lit .unit

def countBody {rT : Type} : Exp rT :=
  match (sourceBody (rT := rT)) with
  | .lam body => body
  | _ => .lit .unit

theorem countBody_lcb {rT : Type} : Exp.lcb 2 (countBody (rT := rT)) = true := by
  lcb_decide

def source {rT : Type} : Val rT := by
  have hc : (Exp.lam (.lam (countBody (rT := rT)))).IsLocallyClosed :=
    Exp.lcb_imp_lc (e := .lam (.lam (countBody (rT := rT))))
      (show Exp.lcb 0 (.lam (.lam (countBody (rT := rT)))) = true from
        countBody_lcb (rT := rT))
  exact ⟨.lam (.lam countBody), .lam hc, hc⟩

theorem source_fst {rT : Type} :
    (source (rT := rT)).fst = Occil.aliasSamples := rfl

def weightedSource {rT : Type} (weights : Val rT) : Val rT := by
  have hc : (Exp.lam (Exp.openRec 1 weights.fst (countBody (rT := rT)))).IsLocallyClosed :=
    Exp.lcb_imp_lc (e := .lam (Exp.openRec 1 weights.fst (countBody (rT := rT))))
      (show Exp.lcb 1 (Exp.openRec 1 weights.fst (countBody (rT := rT))) = true from
        Exp.lcb_openRec (Exp.lcb_ofVal 1 weights) (countBody_lcb (rT := rT)))
  exact ⟨.lam (Exp.openRec 1 weights.fst countBody), .lam hc, hc⟩

def normalizedOpening {rT : Type} (weights : Val rT) (count : ℤ) :
    {e : Exp rT //
      Exp.open' (Exp.openRec 1 weights.fst countBody) (.lit (.int count)) = e} := by
  refine ⟨_, by
    conv_lhs =>
      simp [countBody, sourceBody, Occil.aliasSamples, Exp.open', Exp.openRec,
        Exp.close, Exp.closeRec,
        Var.internal.injEq, ProbLang.openRec_val_fst,
        ArraySyntax.length_openRec, ArraySyntax.length_closeRec,
        WeightedValidation.sumInts_openRec, WeightedValidation.sumInts_closeRec,
        UniformInt.uniformInt_openRec, UniformInt.uniformInt_closeRec,
        ListOperations.repeatSample_openRec, ListOperations.repeatSample_closeRec]⟩

theorem opened_source {rT : Type} (weights : Val rT) (count : ℤ) :
    Exp.open' (Exp.openRec 1 weights.fst countBody) (.lit (.int count)) =
      (normalizedOpening weights count).val :=
  (normalizedOpening weights count).property

end SampLib.AliasSamples
