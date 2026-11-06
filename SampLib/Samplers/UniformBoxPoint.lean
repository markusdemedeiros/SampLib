import SampLib.Distributions.ListProduct
import SampLib.Samplers.UniformInt
import Samplers.General.Points

/-! # Independent uniform points in an integer box -/

open ProbLang
open scoped ENNReal

namespace SampLib.UniformBoxPoint

noncomputable section

section mathematics

open MeasureTheory

/-- Independent coordinates in `[0,scale)`, in their returned order. -/
def law (scale dimension : ℕ) : Measure (List ℕ) :=
  ListProduct.law (fun _ => UniformInt.law scale) 0 dimension

instance (scale dimension : ℕ) [NeZero scale] : IsProbabilityMeasure (law scale dimension) :=
  inferInstanceAs (IsProbabilityMeasure
    (ListProduct.law (fun _ => UniformInt.law scale) 0 dimension))

/-- The tail and the new coordinate retain their independent product expectation. -/
theorem expectation (scale dimension : ℕ) [NeZero scale] (F : List ℕ → ℝ≥0∞) :
    ∫⁻ ys, ∫⁻ x, F (x :: ys) ∂UniformInt.law scale ∂law scale dimension =
      ∫⁻ ys, F ys ∂law scale (dimension + 1) := by
  simpa only [law, ListProduct.constant_start] using
    ListProduct.expectation (fun _ => UniformInt.law scale) 0 dimension F

end mathematics

private theorem encode_cons {rT : Type _} [ProbLangℝ rT] (x : ℕ) (xs : List ℕ) :
    pl(inr(({Exp.ofVal (Val.int (x : ℤ))},
      {Exp.ofVal (listVal (fun n : ℕ => Val.int n) xs)}))) =
      Exp.ofVal (listVal (fun n : ℕ => Val.int n) (x :: xs) : Val rT) := by
  simp [Exp.ofVal, listVal]

private theorem scale_test (scale : ℕ) [NeZero scale] :
    decide ((scale : ℤ) ≤ 0) = false := by simp [NeZero.ne scale]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_uniformBoxPoint (E : CoPset) (scale dimension : ℕ) [NeZero scale]
    (F : List ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ ys, F ys ∂law scale dimension) -∗
      tglWp E pl(&Occil.General.uniformBoxPoint #int (scale : ℤ) #int (dimension : ℤ))
        (fun v : Val rT => iprop(∃ ys : List ℕ,
          ⌜v = listVal (fun n : ℕ => Val.int n) ys⌝ ∗ ↯ (F ys))) := by
  induction dimension generalizing F with
  | zero =>
    iintro Hcredit
    twp_pures
    rw [scale_test]
    simp only [Bool.false_or]
    twp_pures
    twp_value
    imodintro
    iexists []
    isimp only [law, ListProduct.law, MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    ipureintro
    exact Val.ext rfl
  | succ dimension IH =>
    iintro Hcredit
    twp_pures
    rw [scale_test]
    simp only [Bool.false_or]
    iterate 4 twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    twp_bind pl(&Occil.General.uniformBoxPoint #int (scale : ℤ) #int (dimension : ℤ))
    iapply tglWp_wand
    isplitl [Hcredit]
    · isimp only [← expectation scale dimension F] at Hcredit
      iapply (IH (fun ys => ∫⁻ x, F (x :: ys) ∂UniformInt.law scale)) $$ Hcredit
    iintro %v ⟨%ys, %hv, Hcredit⟩
    subst v
    twp_bind pl(&Occil.uniformInt #int (scale : ℤ))
    iapply ((UniformInt.uniformInt_distSpec E scale).wp
      (fun x => F (x :: ys)) (measurable_of_countable _) _) $$ Hcredit
    iintro %x Hcredit
    rw [encode_cons]
    iapply (tglWp_value (v := listVal (fun n : ℕ => Val.int n) (x :: ys)))
    iexists x :: ys
    iframe Hcredit
    itrivial

/-- Every positive side length and nonnegative dimension, including the empty point. -/
theorem uniformBoxPoint_distSpec (E : CoPset) (scale dimension : ℕ) [NeZero scale] :
    IsDistSpec (GF := GF) E
      pl(&Occil.General.uniformBoxPoint #int (scale : ℤ) #int (dimension : ℤ))
      (law scale dimension) (fun ys => listVal (fun n : ℕ => Val.int n) ys) where
  spec F _ := wand_entails (twp_uniformBoxPoint E scale dimension F)

end specification

end

end SampLib.UniformBoxPoint
