import SampLib.PSRN.Support.PSRNSimplexSource
import SampLib.PSRN.Support.LatentRational
import SampLib.Latent.LatentVectorSpec

/-! # The actual simplex singleton branch allocates a constant unit oracle -/

open ProbLang

namespace SampLib.PSRNSimplex

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

def singletonHandles : Fin 1 → Val rT := fun _ => LatentRational.value 1 1

/-- The constant branch leaves every caller resource untouched. -/
theorem twp_singleton (E : CoPset) (P : IProp GF) :
    P ⊢ tglWp E pl(&Occil.PSRN.newSimplex #1 #())
      (fun v => iprop(⌜v = LatentReal.vectorVal singletonHandles⌝ ∗ P)) := by
  iintro HP
  iapply Program.twp_open E 1 _
  unfold Program.openedBody
  twp_pures
  twp_value
  imodintro
  iframe HP
  ipureintro
  apply Val.ext
  simp [LatentReal.vectorVal, singletonHandles, List.ofFn_succ, List.ofFn_zero,
    listVal, LatentRational.value]
  rfl

end

end SampLib.PSRNSimplex
