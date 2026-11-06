import SampLib.Combinatorial.Choice
import Samplers.General.Core
import SampLib.General.Laws.RandomScanGibbs

/-! # Uniform random-scan conditional updates on a countable state space -/

open ProbLang
open scoped ENNReal

namespace SampLib.RandomScanGibbs

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {α : Type _} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
local bi (IProp GF)

attribute [local pl_step_simp] UniformInt.uniformInt_openRec UniformInt.uniformInt_closeRec

private theorem dimension_test (dimension : ℕ) [NeZero dimension] :
    decide ((dimension : ℤ) ≤ 0) = false := by simp [NeZero.ne dimension]

/-- Every update draws a fresh uniform coordinate and then its conditional law. -/
theorem twp_randomScanGibbs (E : CoPset) (dimension : ℕ) [NeZero dimension]
    (conditional : Val rT) (encode : α → Val rT) (K : Fin dimension → α → MeasureTheory.Measure α)
    [∀ i x, MeasureTheory.IsProbabilityMeasure (K i x)]
    (hconditional : ∀ i x,
      IsDistSpec (GF := GF) E pl(&conditional.fst #int (i.val : ℤ) &(encode x).fst)
        (K i x) encode) (n : ℕ) (x : α) (F : α → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂law dimension K n x) -∗
      tglWp E pl(&Occil.General.randomScanGibbs #int (dimension : ℤ)
        &conditional.fst &(encode x).fst #int (n : ℤ))
        (fun v : Val rT => iprop(∃ z : α, ⌜v = encode z⌝ ∗ ↯ (F z))) := by
  induction n generalizing x F with
  | zero =>
    iintro Hcredit
    twp_pures
    rw [dimension_test, Bool.or_false]
    twp_pures
    iapply (tglWp_value_of_toVal (Val.toVal?_fst (encode x)))
    iexists x
    isimp only [law, FiniteKernels.iterate, MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    itrivial
  | succ n ih =>
    iintro Hcredit
    twp_pures
    rw [dimension_test, Bool.or_false]
    iterate 3 twp_pure
    twp_bind pl(&Occil.uniformInt #int (dimension : ℤ))
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply (UniformInt.twp_uniformInt E dimension (NeZero.pos dimension)
        (fun k => ∫⁻ y, (∫⁻ z, F z ∂law dimension K n y)
          ∂K (Choice.position dimension k) x))
      rw [expectation]
      iexact Hcredit
    iintro %v ⟨%k, %hv, %hk, Hcredit⟩
    subst v
    twp_pure
    twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    twp_bind pl(&conditional.fst #int (k : ℤ) &(encode x).fst)
    isimp only [Choice.position_of_lt k hk] at Hcredit
    iapply ((hconditional ⟨k, hk⟩ x).wp
      (fun y => ∫⁻ z, F z ∂law dimension K n y) (measurable_of_countable _) _) $$ Hcredit
    iintro %y Hcredit
    have hnext := ih y F
    simp [Occil.General.randomScanGibbs, Exp.close, Exp.closeRec] at hnext
    exact wand_entails hnext

/-- The finite iterate of the uniform mixture of coordinate kernels. -/
theorem randomScanGibbs_distSpec (E : CoPset) (dimension : ℕ) [NeZero dimension]
    (conditional : Val rT) (encode : α → Val rT) (K : Fin dimension → α → MeasureTheory.Measure α)
    [∀ i x, MeasureTheory.IsProbabilityMeasure (K i x)]
    (hconditional : ∀ i x,
      IsDistSpec (GF := GF) E pl(&conditional.fst #int (i.val : ℤ) &(encode x).fst)
        (K i x) encode) (n : ℕ) (x : α) :
    IsDistSpec (GF := GF) E pl(&Occil.General.randomScanGibbs #int (dimension : ℤ)
      &conditional.fst &(encode x).fst #int (n : ℤ)) (law dimension K n x) encode where
  spec F _ := wand_entails
    (twp_randomScanGibbs E dimension conditional encode K hconditional n x F)

omit [ProbLangDist.IsUniformInt rT] in
/-- Zero updates return the initial value without invoking the conditional sampler. -/
theorem randomScanGibbs_zero_distSpec (E : CoPset) (dimension : ℕ) [NeZero dimension]
    (conditional initial : Val rT) :
    IsDistSpec (GF := GF) E pl(&Occil.General.randomScanGibbs #int (dimension : ℤ)
      &conditional.fst &initial.fst #0)
      (MeasureTheory.Measure.dirac ()) (fun _ : Unit => initial) where
  spec F _ := by
    iintro Hcredit
    twp_pures
    rw [dimension_test, Bool.or_false]
    twp_pures
    iapply (tglWp_value_of_toVal (Val.toVal?_fst initial))
    iexists ()
    isimp only [MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    itrivial

end specification

end

end SampLib.RandomScanGibbs
