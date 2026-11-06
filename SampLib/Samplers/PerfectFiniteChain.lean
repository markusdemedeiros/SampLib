import SampLib.Samplers.CouplingFromPast
import SampLib.Samplers.TypedRandomMap

/-! # Perfect sampling from an integer-weighted finite transition matrix

The concrete shared-map sampler supplies the random-mapping law for CFTP. The
primary contract is stationarity and a positive finite coalescent word, allowing
transition matrices with zeros and mappings that do not coalesce in one step.
-/

open ProbLang
open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal

namespace SampLib.PerfectFiniteChain

noncomputable section

open CouplingFromPast

private abbrev callback {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
    (rows : List MarkovChain.Row) : Val rT :=
  ⟨.lam (.app (.app Occil.General.randomMap (listVal RandomMap.encodeRow rows).fst)
    (.lit .unit)), .lam (by is_lc), by is_lc⟩

private theorem randomMap_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.General.randomMap = Occil.General.randomMap :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem randomMap_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.General.randomMap : Exp rT) = Occil.General.randomMap :=
  Exp.closeRec_fresh x _ k (by
    simp [Occil.General.randomMap, Occil.weightedChoice, Occil.sumInts,
      Occil.uniformInt, Exp.fv])

private theorem coupling_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.General.couplingFromPast = Occil.General.couplingFromPast :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem coupling_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.General.couplingFromPast : Exp rT) =
      Occil.General.couplingFromPast := Exp.closeRec_fresh x _ k (by
        simp [Occil.General.couplingFromPast, Exp.fv, applyMaps_fv, applyMaps_closeRec,
          ListOperations.append_fv, ListOperations.append_closeRec,
          ListOperations.repeatSample_fv, ListOperations.repeatSample_closeRec])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] randomMap_openRec randomMap_closeRec
  coupling_openRec coupling_closeRec

private theorem callback_distSpec (E : CoPset) (rows : List MarkovChain.Row)
    [NeZero rows.length] (hsquare : ∀ r ∈ rows, r.val.length = rows.length) :
    IsDistSpec (GF := GF) E pl(&(callback rows).fst #()) (RandomMapSupport.law rows) mapVal where
  spec F hF := by
    iintro Hcredit
    twp_pure
    twp_bind pl(&Occil.General.randomMap &(listVal RandomMap.encodeRow rows).fst #())
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply (RandomMapSupport.typedRandomMap_distSpec E rows hsquare).spec F hF $$ Hcredit

/-- Exact matrix-stationary sampling for every coalescent iid shared-map representation. -/
theorem perfectFiniteChain_distSpec (E : CoPset) (rows : List MarkovChain.Row)
    [NeZero rows.length] (hsquare : ∀ r ∈ rows, r.val.length = rows.length)
    (π : Measure (Fin rows.length)) [IsProbabilityMeasure π]
    (hπ : π.bind (RandomMapSupport.kernel rows) = π)
    (hcoal : ∃ L, 0 < (IIDList.law (RandomMapSupport.law rows) L)
      {maps | Coalesces maps}) :
    IsDistSpec (GF := GF) E pl(&Occil.General.perfectFiniteChain
      &(listVal RandomMap.encodeRow rows).fst #()) π stateVal where
  spec F hF := by
    iintro Hcredit
    iterate 2 twp_pure
    twp_bind pl(&Occil.length &(listVal RandomMap.encodeRow rows).fst)
    iapply tglWp_wand
    isplitl []
    · iapply twp_length E RandomMap.encodeRow rows
    iintro %v %hv
    subst v
    simp only [Exp.ofVal]
    twp_bind pl(&Occil.General.couplingFromPast #int (rows.length : ℤ) &(callback rows).fst #())
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply (couplingFromPast_distSpec E (RandomMapSupport.law rows) π
      (RandomMapSupport.stationary rows π hπ) hcoal (callback rows)
      (callback_distSpec E rows hsquare)).spec F hF $$ Hcredit

end specification

end

end SampLib.PerfectFiniteChain
