import SampLib.Core.BetaStep
import Samplers.PSRN.Core

/-! # The actual integer-grid observation loop with a fixed source handle -/

open ProbLang

namespace SampLib.LatentReal.Floor.Program

/-- Structural binders keep the source handle's free variables untouched. -/
def loopCode {rT : Type} (source : Exp rT) (scale : ℤ) : Exp rT :=
  let bind (rhs body : Exp rT) := .app (.lam body) rhs
  let lo := .binop .div (.binop .mult (.fst (.bvar 1)) (.lit (.int scale)))
    (.snd (.bvar 0))
  let hi := .binop .div (.binop .mult (.fst (.bvar 1)) (.lit (.int scale)))
    (.snd (.bvar 1))
  let retry := .app (.bvar 5) (.binop .plus (.bvar 4) (.lit (.int 1)))
  let branch := .cond (.binop .eq (.bvar 1) (.bvar 0)) (.bvar 1) retry
  .fix (.lam (bind (.app source (.bvar 0))
    (bind (.snd (.bvar 0)) (bind lo (bind hi branch)))))

def loop {rT : Type} (source : Val rT) (scale : ℤ) : Exp rT := loopCode source.fst scale

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

/-- Open the checked positive-scale constructor and retain its named refinement loop. -/
theorem twp_open (E : CoPset) (source : Val rT) (scale : ℤ) (hscale : 0 < scale)
    (Φ : Val rT → IProp GF) :
    tglWp E pl(&(loop source scale) #1) Φ ⊢
      tglWp E pl(&Occil.PSRN.floorScaled &source.fst #scale) Φ := by
  iintro H
  iterate 3 twp_pure
  rw [decide_eq_false (not_le.mpr hscale)]
  iterate 2 twp_pure
  ieval (change _ ⊢ tglWp E pl(&(loop source scale) #1) Φ)
  iexact H

end specification

end SampLib.LatentReal.Floor.Program
