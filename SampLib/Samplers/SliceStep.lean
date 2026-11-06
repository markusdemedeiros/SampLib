import SampLib.Distributions.Slice
import SampLib.FiniteGridSpec
import SampLib.Syntax.Rejection
import Samplers.General.Core

/-! # A finite-grid slice transition

The starting value may lie outside the grid. Its positive height cap must be
bounded by some grid weight, so every sampled slice has an accepted point.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.SliceStep

noncomputable section

def encode {rT : Type _} {width : ℕ} (lower : ℤ) (i : Fin width) : Val rT :=
  Val.int (FiniteGrid.point lower i)

/-- Insert the density callback after closing the predicate's own binder. -/
private def accept {rT : Type _} (height : ℕ) (density : Val rT) : Val rT := by
  let e : Exp rT := pl(fun x, #int (height : ℤ) < density x)
  have hlc := Exp.subst_lc (x := .named "density")
    (by is_lc : e.IsLocallyClosed) density.lc
  exact ⟨Exp.subst e (.named "density") density.fst, .lam hlc, hlc⟩

private theorem height_test (h weight : ℕ) :
    decide ((h : ℤ) < (weight : ℤ)) = decide (h < weight) := by simp

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] UniformInt.uniformInt_openRec UniformInt.uniformInt_closeRec
  RndIntExcRange.rndIntExcRange_openRec RndIntExcRange.rndIntExcRange_closeRec
  Rejection.rejection_openRec Rejection.rejection_closeRec

omit [ProbLangDist.IsUniformInt rT] in
private theorem accept_spec (E : CoPset) (height : ℕ) (density : Val rT)
    (lower : ℤ) (width : ℕ) (w : Fin width → ℕ)
    (hdensity : ∀ i, ⊢ tglWp E pl(&density.fst &(encode lower i).fst)
      (fun v : Val rT => iprop(⌜v = Val.int (w i)⌝))) (i : Fin width) :
    ⊢ tglWp E pl(&(accept height density).fst &(encode lower i).fst)
      (fun v : Val rT => iprop(⌜v = Val.bool (decide (height < w i))⌝)) := by
  isimp [accept, Exp.subst, Exp.close, Exp.closeRec]
  twp_pure
  twp_bind pl(&density.fst &(encode lower i).fst)
  iapply tglWp_wand
  isplitl []
  · iapply hdensity i
  iintro %v %hv
  subst v
  twp_pures
  rw [height_test]
  twp_value
  imodintro
  ipureintro
  rfl

/-- Every bounded slice is sampled uniformly by the verified rejection combinator. -/
private theorem twp_rejection (E : CoPset) (height : ℕ) (density : Val rT)
    (lower : ℤ) (width : ℕ) [NeZero width] (w : Fin width → ℕ)
    (hdensity : ∀ i, ⊢ tglWp E pl(&density.fst &(encode lower i).fst)
      (fun v : Val rT => iprop(⌜v = Val.int (w i)⌝)))
    (hne : (SliceLaw.level w height).Nonempty) (F : Fin width → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ i, F i ∂MeasureTheory.Measure.uniformOfFinset (SliceLaw.level w height)) -∗
      tglWp E
        pl(&Occil.rejection &(FiniteGrid.proposal lower width).fst &(accept height density).fst #())
      (fun v : Val rT => iprop(∃ i : Fin width, ⌜v = encode lower i⌝ ∗ ↯ (F i))) := by
  have h := Rejection.twp_rejection (GF := GF) E (FiniteGrid.law width) {i | height < w i}
    (Set.to_countable _).measurableSet (SliceLaw.acceptance_nonzero w height hne)
    (encode lower) (FiniteGrid.proposal lower width) (accept height density)
    (FiniteGrid.proposal_distSpec E lower width)
    (fun i => accept_spec E height density lower width w hdensity i) F (measurable_of_countable _)
  simpa only [Rejection.credit, Rejection.law, FiniteGrid.law,
    SliceLaw.conditioned_uniform w height hne] using h

/-- Slice sampling preserves the height mixture's continuation credit. -/
theorem twp_sliceStep (E : CoPset) (density initial : Val rT) (lower : ℤ)
    (width : ℕ) [NeZero width] (w : Fin width → ℕ) (cap : ℕ) (hcap : 0 < cap)
    (hanchor : ∃ i, cap ≤ w i)
    (hinitial : ⊢ tglWp E pl(&density.fst &initial.fst)
      (fun v : Val rT => iprop(⌜v = Val.int cap⌝)))
    (hdensity : ∀ i, ⊢ tglWp E pl(&density.fst &(encode lower i).fst)
      (fun v : Val rT => iprop(⌜v = Val.int (w i)⌝))) (F : Fin width → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ i, F i ∂SliceLaw.stepLaw w cap hcap hanchor) -∗
      tglWp E pl(&Occil.General.sliceStep &density.fst #lower #int (lower + (width : ℤ))
        &initial.fst)
        (fun v : Val rT => iprop(∃ i : Fin width, ⌜v = encode lower i⌝ ∗ ↯ (F i))) := by
  have hlevels := (SliceLaw.levels_nonempty_iff w cap hcap).mpr hanchor
  iintro Hcredit
  iterate 4 twp_pure
  twp_bind pl(&density.fst &initial.fst)
  iapply tglWp_wand
  isplitl []
  · iapply hinitial
  iintro %v %hv
  subst v
  twp_bind pl(&Occil.uniformInt #int (cap : ℤ))
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply (UniformInt.twp_uniformInt E cap hcap
      (fun height => ∫⁻ i, F i ∂MeasureTheory.Measure.uniformOfFinset (SliceLaw.level w height)))
    rw [SliceLaw.stepLaw_expectation w cap hcap hanchor F]
    iexact Hcredit
  iintro %v ⟨%height, %hv, %hh, Hcredit⟩
  subst v
  iterate 2 twp_pure
  have hnext := twp_rejection E height density lower width w hdensity (hlevels height hh) F
  simp [FiniteGrid.proposal, accept, Exp.subst, Exp.close, Exp.closeRec] at hnext
  exact wand_entails hnext

/-- The complete positive-cap domain, including starting values outside the proposal grid. -/
theorem sliceStep_distSpec (E : CoPset) (density initial : Val rT) (lower : ℤ)
    (width : ℕ) [NeZero width] (w : Fin width → ℕ) (cap : ℕ) (hcap : 0 < cap)
    (hanchor : ∃ i, cap ≤ w i)
    (hinitial : ⊢ tglWp E pl(&density.fst &initial.fst)
      (fun v : Val rT => iprop(⌜v = Val.int cap⌝)))
    (hdensity : ∀ i, ⊢ tglWp E pl(&density.fst &(encode lower i).fst)
      (fun v : Val rT => iprop(⌜v = Val.int (w i)⌝))) :
    IsDistSpec (GF := GF) E
      pl(&Occil.General.sliceStep &density.fst #lower #int (lower + (width : ℤ)) &initial.fst)
      (SliceLaw.stepLaw w cap hcap hanchor) (encode lower) where
  spec F _ := wand_entails
    (twp_sliceStep E density initial lower width w cap hcap hanchor hinitial hdensity F)

/-- For a positive grid state, the height mixture is the canonical slice kernel. -/
theorem sliceStep_grid_distSpec (E : CoPset) (density : Val rT) (lower : ℤ)
    (width : ℕ) [NeZero width] (w : Fin width → ℕ)
    (hdensity : ∀ i, ⊢ tglWp E pl(&density.fst &(encode lower i).fst)
      (fun v : Val rT => iprop(⌜v = Val.int (w i)⌝))) (x : Fin width) (hx : 0 < w x) :
    IsDistSpec (GF := GF) E pl(&Occil.General.sliceStep &density.fst #lower
      #int (lower + (width : ℤ)) &(encode lower x).fst) (SliceLaw.kernel w x) (encode lower) := by
  simpa only [SliceLaw.kernel, ite_eq_left hx, SliceLaw.stepLaw] using
    sliceStep_distSpec E density (encode lower x) lower width w (w x) hx ⟨x, le_rfl⟩
      (hdensity x) hdensity

end specification

end

end SampLib.SliceStep
