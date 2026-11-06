import SampLib.Core.CurriedStep
import SampLib.Latent.LatentVectorSpec
import SampLib.PSRN.Support.LatentRational
import Samplers.PSRN.Geometry

/-! # The actual singleton branches of Dirichlet and simplex construction -/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.NormalizedSingleton

noncomputable section

def handles {rT : Type} : Fin 1 → Val rT := fun _ => LatentRational.value 1 1

def shapeVal {rT : Type} [ProbLangℝ rT] (a b : ℕ) : Val rT :=
  listVal id [Val.pair (Val.int (a : ℤ)) (Val.int (b : ℤ))]

private theorem valid_shape (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Bool.or (decide ((a : ℤ) ≤ 0)) (decide ((b : ℤ) ≤ 0)) = false := by
  simp [ha.ne', hb.ne']

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private def body (yes no : Exp rT) : Exp rT :=
  .cond (.binop .le (.bvar 1) (.lit (.int 0))) .fail
    (.cond (.binop .eq (.bvar 1) (.lit (.int 1))) yes no)

private def sourceBody : Exp rT :=
  match (Occil.PSRN.newSimplex : Exp rT) with
  | .lam (.lam result) => result
  | _ => .fail

private def yes : Exp rT :=
  match (sourceBody : Exp rT) with
  | .cond _ _ (.cond _ result _) => result
  | _ => .fail

private def no : Exp rT :=
  match (sourceBody : Exp rT) with
  | .cond _ _ (.cond _ _ result) => result
  | _ => .fail

private theorem source_eq : (Occil.PSRN.newSimplex : Exp rT) =
    CurriedStep.lambdas 2 sourceBody := by kernel_rfl

private theorem sourceBody_eq : (sourceBody : Exp rT) = body yes no := by kernel_rfl

private theorem sourceBody_lcb : Exp.lcb 2 (sourceBody : Exp rT) = true := by lcb_decide

private def opened (e : Exp rT) : Exp rT :=
  Exp.openRec 0 (.lit .unit) (Exp.openRec 1 (.lit (.int 1)) e)

private def afterFirst (a b : Exp rT) : Exp rT :=
  .cond (.binop .eq (.lit (.int 1)) (.lit (.int 1))) (opened a) (opened b)

private theorem opened_body (a b : Exp rT) :
    CurriedStep.opened [.int 1, .unit] (body a b) =
      .cond (.binop .le (.lit (.int 1)) (.lit (.int 0))) .fail (afterFirst a b) := rfl

/-- The singleton simplex captures an exact unit oracle and preserves every resource. -/
theorem twp_newSimplex_one (E : CoPset) (P : IProp GF) :
    P ⊢ tglWp E pl(&Occil.PSRN.newSimplex #1 #())
      (fun v => iprop(⌜v = vectorVal handles⌝ ∗ P)) := by
  have hopen := CurriedStep.twp_apply E [] [.int 1, .unit] (sourceBody (rT := rT))
    (sourceBody_lcb (rT := rT)) (fun v => iprop(⌜v = vectorVal handles⌝ ∗ P))
  rw [sourceBody_eq, opened_body] at hopen
  iintro HP
  iapply hopen
  twp_pure
  iapply (twp_pure_step_fupd (e₂ := afterFirst (yes (rT := rT)) no) True trivial)
  twp_pure
  iapply (twp_pure_step_fupd (e₂ := opened (yes (rT := rT))) True trivial)
  twp_pures
  twp_value
  imodintro
  iframe HP
  ipureintro
  apply Val.ext
  simp [vectorVal, handles, List.ofFn_succ, List.ofFn_zero, listVal, LatentRational.value]

end specification

end

end SampLib.LatentReal.NormalizedSingleton
