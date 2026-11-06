import SampLib.Samplers.SampleWithReplacement
import Samplers.General.Core

/-! # Paths of random walks with independent integer increments -/

open ProbLang
open scoped ENNReal

namespace SampLib.RandomWalkPath

noncomputable section

section mathematics

open MeasureTheory

/-- Scan the independent increment vector, retaining the initial position. -/
def law (μ : Measure ℤ) (initial : ℤ) (steps : ℕ) : Measure (List ℤ) :=
  (SampleWithReplacement.law μ steps).map (fun xs => (List.ofFn xs).scanl (· + ·) initial)

instance (μ : Measure ℤ) [IsProbabilityMeasure μ] (initial : ℤ) (steps : ℕ) :
    IsProbabilityMeasure (law μ initial steps) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- The first increment shifts the remaining path and preserves the starting point. -/
theorem expectation (μ : Measure ℤ) [IsProbabilityMeasure μ] (initial : ℤ)
    (steps : ℕ) (F : List ℤ → ℝ≥0∞) :
    ∫⁻ x, ∫⁻ ys, F (initial :: ys) ∂law μ (initial + x) steps ∂μ =
      ∫⁻ ys, F ys ∂law μ initial (steps + 1) := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    SampleWithReplacement.lintegral_law_succ μ steps _ (measurable_of_countable _)]
  simp only [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    List.ofFn_succ, List.scanl_cons, Fin.cons_zero, Fin.cons_succ]

end mathematics

private theorem encode_cons {rT : Type _} [ProbLangℝ rT] (initial : ℤ) (ys : List ℤ) :
    pl(inr((#int initial, {Exp.ofVal (listVal (fun z : ℤ => (Val.int z : Val rT)) ys)}))) =
      Exp.ofVal (listVal (fun z : ℤ => (Val.int z : Val rT)) (initial :: ys)) := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_randomWalkPath (E : CoPset) (μ : MeasureTheory.Measure ℤ)
    [MeasureTheory.IsProbabilityMeasure μ] (increment : Val rT)
    (hincrement : IsDistSpec (GF := GF) E pl(&increment.fst #()) μ Val.int)
    (initial : ℤ) (steps : ℕ) (F : List ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ ys, F ys ∂law μ initial steps) -∗
      tglWp E pl(&Occil.General.randomWalkPath &increment.fst #int initial #int (steps : ℤ))
        (fun v : Val rT => iprop(∃ ys : List ℤ,
          ⌜v = listVal (fun z : ℤ => Val.int z) ys⌝ ∗ ↯ (F ys))) := by
  induction steps generalizing initial F with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists [initial]
    isimp only [law, SampleWithReplacement.law, MeasureTheory.lintegral_map
      (measurable_of_countable _) (measurable_of_countable _),
      MeasureTheory.lintegral_dirac, List.ofFn_zero, List.scanl_nil] at Hcredit
    iframe Hcredit
    ipureintro
    rfl
  | succ steps IH =>
    iintro Hcredit
    twp_pures
    rw [Nat.cast_add_one, add_sub_cancel_right]
    twp_bind pl(&increment.fst #())
    isimp only [← expectation μ initial steps F] at Hcredit
    iapply (hincrement.wp (fun x => ∫⁻ ys, F (initial :: ys) ∂law μ (initial + x) steps)
      (measurable_of_countable _) _) $$ Hcredit
    iintro %x Hcredit
    twp_pure
    twp_bind pl(&Occil.General.randomWalkPath &increment.fst #int (initial + x)
      #int (steps : ℤ))
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply IH $$ Hcredit
    iintro %v ⟨%ys, %hv, Hcredit⟩
    subst v
    rw [encode_cons initial ys]
    iapply (tglWp_value (v := listVal (fun z : ℤ => Val.int z) (initial :: ys)))
    iexists initial :: ys
    iframe Hcredit
    ipureintro
    rfl

/-- Typed path law, including zero steps and arbitrary signed initial positions. -/
theorem randomWalkPath_distSpec (E : CoPset) (μ : MeasureTheory.Measure ℤ)
    [MeasureTheory.IsProbabilityMeasure μ] (increment : Val rT)
    (hincrement : IsDistSpec (GF := GF) E pl(&increment.fst #()) μ Val.int)
    (initial : ℤ) (steps : ℕ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.General.randomWalkPath &increment.fst #int initial #int (steps : ℤ))
      (law μ initial steps) (listVal (fun z : ℤ => Val.int z)) where
  spec F _ := wand_entails (twp_randomWalkPath E μ increment hincrement initial steps F)

end specification

end

end SampLib.RandomWalkPath
