import SampLib.Samplers.SliceStep
import SampLib.SliceTerms

/-! # Finite iteration of the slice kernel

A positive grid state follows the canonical transition law. An arbitrary initial
value first enters the grid through its valid height cap, then follows that law.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.SliceSampler

noncomputable section

section mathematics

open MeasureTheory

/-- One initialization transition, followed by the remaining grid transitions. -/
def initialLaw {width : ℕ} (w : Fin width → ℕ) (cap : ℕ) (hcap : 0 < cap)
    (hanchor : ∃ i, cap ≤ w i) (n : ℕ) : Measure (Fin width) :=
  (SliceLaw.stepLaw w cap hcap hanchor).bind (SliceLaw.law w n)

instance {width : ℕ} (w : Fin width → ℕ) (cap : ℕ) (hcap : 0 < cap)
    (hanchor : ∃ i, cap ≤ w i) (n : ℕ) :
    IsProbabilityMeasure (initialLaw w cap hcap hanchor n) where
  measure_univ := by
    rw [initialLaw, Measure.bind_apply MeasurableSet.univ
      (measurable_of_countable _).aemeasurable]
    simp

theorem initial_expectation {width : ℕ} (w : Fin width → ℕ) (cap : ℕ) (hcap : 0 < cap)
    (hanchor : ∃ i, cap ≤ w i) (n : ℕ) (F : Fin width → ℝ≥0∞) :
    ∫⁻ y, (∫⁻ z, F z ∂SliceLaw.law w n y) ∂SliceLaw.stepLaw w cap hcap hanchor =
      ∫⁻ z, F z ∂initialLaw w cap hcap hanchor n := by
  rw [initialLaw, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open SliceStep (encode)

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] SliceTerms.sliceStep_openRec SliceTerms.sliceStep_closeRec

/-- Each positive grid state supplies the next slice transition and its continuation. -/
theorem twp_sliceSampler (E : CoPset) (density : Val rT) (lower : ℤ)
    (width : ℕ) [NeZero width] (w : Fin width → ℕ)
    (hdensity : ∀ i, ⊢ tglWp E pl(&density.fst &(encode lower i).fst)
      (fun v : Val rT => iprop(⌜v = Val.int (w i)⌝)))
    (n : ℕ) (x : Fin width) (hx : 0 < w x) (F : Fin width → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ i, F i ∂SliceLaw.law w n x) -∗
      tglWp E pl(&Occil.General.sliceSampler &density.fst #lower
        #int (lower + (width : ℤ)) &(encode lower x).fst #int (n : ℤ))
        (fun v : Val rT => iprop(∃ i : Fin width, ⌜v = encode lower i⌝ ∗ ↯ (F i))) := by
  induction n generalizing x F with
  | zero =>
    iintro Hcredit
    iterate 10 twp_pure
    iapply (tglWp_value_of_toVal (Val.toVal?_fst (encode lower x)))
    iexists x
    isimp only [SliceLaw.law, FiniteKernels.iterate, MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    itrivial
  | succ n ih =>
    iintro Hcredit
    iterate 11 twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    twp_bind pl(&Occil.General.sliceStep &density.fst #lower
      #int (lower + (width : ℤ)) &(encode lower x).fst)
    isimp only [← FiniteKernels.expectation] at Hcredit
    iapply ((SliceStep.sliceStep_grid_distSpec E density lower width w hdensity x hx).wp_supported
      (fun y => 0 < w y) (Set.to_countable _).measurableSet (SliceLaw.ae_positive w x hx)
      (fun y => ∫⁻ z, F z ∂SliceLaw.law w n y) (measurable_of_countable _) _) $$ Hcredit
    iintro %y %hy Hcredit
    have hnext := ih y hy F
    simp [Occil.General.sliceSampler, Exp.close, Exp.closeRec] at hnext
    exact wand_entails hnext

/-- The requested finite iterate, with the target invariant by `SliceLaw.iterate_invariant`. -/
theorem sliceSampler_distSpec (E : CoPset) (density : Val rT) (lower : ℤ)
    (width : ℕ) [NeZero width] (w : Fin width → ℕ)
    (hdensity : ∀ i, ⊢ tglWp E pl(&density.fst &(encode lower i).fst)
      (fun v : Val rT => iprop(⌜v = Val.int (w i)⌝)))
    (n : ℕ) (x : Fin width) (hx : 0 < w x) :
    IsDistSpec (GF := GF) E pl(&Occil.General.sliceSampler &density.fst #lower
      #int (lower + (width : ℤ)) &(encode lower x).fst #int (n : ℤ))
      (SliceLaw.law w n x) (encode lower) where
  spec F _ := wand_entails (twp_sliceSampler E density lower width w hdensity n x hx F)

/-- A valid outside-grid start enters once, then performs the remaining grid transitions. -/
theorem sliceSampler_start_distSpec (E : CoPset) (density initial : Val rT) (lower : ℤ)
    (width : ℕ) [NeZero width] (w : Fin width → ℕ) (cap : ℕ) (hcap : 0 < cap)
    (hanchor : ∃ i, cap ≤ w i)
    (hinitial : ⊢ tglWp E pl(&density.fst &initial.fst)
      (fun v : Val rT => iprop(⌜v = Val.int cap⌝)))
    (hdensity : ∀ i, ⊢ tglWp E pl(&density.fst &(encode lower i).fst)
      (fun v : Val rT => iprop(⌜v = Val.int (w i)⌝))) (n : ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.General.sliceSampler &density.fst #lower
      #int (lower + (width : ℤ)) &initial.fst #int ((n + 1 : ℕ) : ℤ))
      (initialLaw w cap hcap hanchor n) (encode lower) where
  spec F _ := by
    iintro Hcredit
    iterate 11 twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    twp_bind pl(&Occil.General.sliceStep &density.fst #lower
      #int (lower + (width : ℤ)) &initial.fst)
    isimp only [← initial_expectation] at Hcredit
    iapply ((SliceStep.sliceStep_distSpec E density initial lower width w cap hcap hanchor
      hinitial hdensity).wp_supported (fun y => 0 < w y) (Set.to_countable _).measurableSet
      (SliceLaw.heightMixture_ae_positive w cap)
      (fun y => ∫⁻ z, F z ∂SliceLaw.law w n y) (measurable_of_countable _) _) $$ Hcredit
    iintro %y %hy Hcredit
    have hnext := twp_sliceSampler E density lower width w hdensity n y hy F
    simp [Occil.General.sliceSampler, Exp.close, Exp.closeRec] at hnext
    exact wand_entails hnext

omit [ProbLangDist.IsUniformInt rT] in
/-- Zero transitions return any initial value without inspecting the density or bounds. -/
theorem sliceSampler_zero_distSpec (E : CoPset) (density lower upper initial : Val rT) :
    IsDistSpec (GF := GF) E pl(&Occil.General.sliceSampler &density.fst &lower.fst
      &upper.fst &initial.fst #0) (MeasureTheory.Measure.dirac ()) (fun _ : Unit => initial) where
  spec F _ := by
    iintro Hcredit
    iterate 10 twp_pure
    iapply (tglWp_value_of_toVal (Val.toVal?_fst initial))
    iexists ()
    isimp only [MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    itrivial

end specification

end

end SampLib.SliceSampler
