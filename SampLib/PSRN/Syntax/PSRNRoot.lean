import SampLib.Latent.LatentViews
import SampLib.Core.Syntax.ClosedExp
import Samplers.PSRN.Arithmetic

/-! # The fixed-source root closure returned by the actual constructor -/

open ProbLang

namespace SampLib.LatentReal.Root.Program

def observerBody {rT : Type} : Exp rT :=
  match (Occil.PSRN.root : Exp rT) with
  | .lam (.lam (.cond _ _ (.cond _ _ (.lam body)))) => body
  | _ => .fail

private theorem observerBody_lcb {rT : Type} : Exp.lcb 3 (observerBody : Exp rT) = true := by
  kernel_rfl

/-- The constructor's guards, with the observer body left opaque. -/
private theorem root_eq {rT : Type} : (Occil.PSRN.root : Exp rT) =
    .lam (.lam (.cond pl({Exp.bvar 0} <= #0) .fail
      (.cond pl({Exp.bvar 0} = #1) (.bvar 1) (.lam observerBody)))) := by
  kernel_rfl

/-- Open the two constructor parameters beneath the retained precision binder. -/
def code {rT : Type} (source : Val rT) (degree : ℕ) : Exp rT :=
  .lam (Exp.openRec 1 (.lit (.int (degree : ℤ))) (Exp.openRec 2 source.fst observerBody))

private theorem code_lc {rT : Type} (source : Val rT) (degree : ℕ) :
    (code source degree).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  change Exp.lcb 1 _ = true
  apply Exp.lcb_openRec (by rfl)
  exact Exp.lcb_openRec
    (Exp.lcb_mono (Exp.lc_imp_lcb source.lc) (by omega)) observerBody_lcb

/-- The source oracle is captured once; observing the root retains that handle. -/
def value {rT : Type} (source : Val rT) (degree : ℕ) : Val rT :=
  ⟨code source degree, .lam (code_lc source degree), code_lc source degree⟩

private theorem int_beq {rT : Type} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
variable {S : Type}
local bi (IProp GF)

attribute [local irreducible] observerBody in
/-- Constructing a nontrivial root only captures its source and degree. -/
theorem twp_root (E : CoPset) (source : Val rT) (degree : ℕ) (hdegree : 2 ≤ degree)
    (P : S → IProp GF) (s : S) :
    iprop(P s) ⊢ tglWp E pl(&Occil.PSRN.root &source.fst #int (degree : ℤ))
      (fun v => ViewOwns (value source degree) P v s) := by
  iintro Hstate
  rw [root_eq]
  twp_pures
  rw [decide_eq_false (show ¬(degree : ℤ) ≤ 0 by omega)]
  twp_pures
  rw [int_beq, beq_eq_false_iff_ne.mpr (show (degree : ℤ) ≠ 1 by omega)]
  twp_pures
  twp_value
  imodintro
  isimp only [ViewOwns]
  iframe Hstate
  ipureintro
  apply Val.ext
  have hs (k : ℕ) (e : Exp rT) : Exp.openRec k e source.fst = source.fst :=
    (Exp.open_lc k e source.fst source.lc).symm
  simp [value, code, observerBody, Occil.PSRN.root, hs]

end specification

end SampLib.LatentReal.Root.Program
