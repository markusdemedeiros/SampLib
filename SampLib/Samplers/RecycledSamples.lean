import SampLib.Samplers.RecycledUniform
import SampLib.ListOperations
import SampLib.Syntax.ClosedExp

/-! # Independent uniform draws from one freshly allocated entropy pool

The fresh pool `(0,1)` is reset after every draw, so each draw has the same
owned uniform specification. Owned repetition then gives independent outputs.
-/

open ProbLang MeasureTheory
open scoped ENNReal

namespace SampLib.RecycledSamples

noncomputable section

/-- Independent uniform draws on `[0,n)`, decoded as a list in sampling order. -/
def law (n count : ℕ) : Measure (List ℕ) :=
  (SampleWithReplacement.law (UniformInt.law n) count).map List.ofFn

instance (n count : ℕ) [NeZero n] : IsProbabilityMeasure (law n count) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

theorem expectation (n count : ℕ) (F : List ℕ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ xs, F (List.ofFn xs) ∂SampleWithReplacement.law (UniformInt.law n) count =
      ∫⁻ ys, F ys ∂law n count := by
  rw [law, lintegral_map hF (measurable_of_countable _)]

private def draw {rT : Type} (pool : Loc) (n : ℕ) : Val rT :=
  ⟨.lam pl(&Occil.Weighted.recycledUniform #loc pool #int (n : ℤ)), .lam (by is_lc), by is_lc⟩

private instance uniform_closed {rT : Type} :
    ClosedExp (Occil.Weighted.recycledUniform : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.Weighted.recycledUniform, Exp.fv]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem draw_ownedSpec (E : CoPset) (pool : Loc) (n : ℕ) [NeZero n] :
    IsOwnedDistSpec (GF := GF) E (appHeapFrag pool (EntropyPool.poolVal (rT := rT) 0 1))
      pl(&(draw (rT := rT) pool n).fst #()) (UniformInt.law n)
      (fun r : ℕ => Val.int (r : ℤ)) where
  spec F hF := by
    iintro Hinput
    twp_pure
    simp only [ClosedExp.openRec]
    iapply (RecycledUniform.recycledUniform_ownedDistSpec E pool n).spec F hF $$ Hinput

/-- Every nonnegative count, including zero, and every positive bound. -/
theorem recycledSamples_distSpec (E : CoPset) (n count : ℕ) [NeZero n] :
    IsDistSpec (GF := GF) E
      pl(&Occil.Weighted.recycledSamples #int (n : ℤ) #int (count : ℤ))
      (law n count) (fun xs => listVal (fun r : ℕ => (Val.int r : Val rT)) xs) where
  spec F hF := by
    iintro Hcredit
    isimp only [← expectation n count F hF] at Hcredit
    twp_pures
    simp only [ClosedExp.openRec, ClosedExp.closeRec, ListOperations.repeatSample_openRec,
      ListOperations.repeatSample_closeRec]
    twp_bind pl(alloc((#0, #1)))
    ieval (change _ ⊢ tglWp E (.alloc (.ofVal (EntropyPool.poolVal (rT := rT) 0 1))) _)
    iapply (twp_alloc (v := EntropyPool.poolVal (rT := rT) 0 1))
    iintro %pool Hpool
    twp_pure
    simp only [ClosedExp.openRec, ListOperations.repeatSample_openRec]
    have hrepeat := repeatSample_ownedDistSpec (GF := GF) E
      (appHeapFrag pool (EntropyPool.poolVal (rT := rT) 0 1)) (UniformInt.law n)
      (fun r : ℕ => (Val.int r : Val rT)) (draw pool n) (draw_ownedSpec E pool n) count
    simp only [draw] at hrepeat
    iapply tglWp_wand
    isplitl [Hpool Hcredit]
    · iapply hrepeat.spec (fun xs => F (List.ofFn xs)) (measurable_of_countable _)
      iframe Hpool Hcredit
    iintro %v ⟨%xs, %hv, -, Hcredit⟩
    iexists List.ofFn xs
    iframe %hv Hcredit

/-- A zero count never reads the pool, so it returns the empty list for every integer bound. -/
theorem recycledSamples_zero_distSpec (E : CoPset) (n : ℤ) :
    IsDistSpec (GF := GF) E pl(&Occil.Weighted.recycledSamples #int n #int (0 : ℤ))
      (Measure.dirac ([] : List ℕ)) (fun xs => listVal (fun r : ℕ => (Val.int r : Val rT)) xs) where
  spec F _ := by
    iintro Hcredit
    isimp only [lintegral_dirac] at Hcredit
    twp_pures
    simp only [ClosedExp.openRec, ClosedExp.closeRec, ListOperations.repeatSample_openRec,
      ListOperations.repeatSample_closeRec]
    twp_bind pl(alloc((#0, #1)))
    ieval (change _ ⊢ tglWp E (.alloc (.ofVal (EntropyPool.poolVal (rT := rT) 0 1))) _)
    iapply (twp_alloc (v := EntropyPool.poolVal (rT := rT) 0 1))
    iintro %pool -
    twp_pure
    simp only [ClosedExp.openRec, ListOperations.repeatSample_openRec]
    twp_pures
    twp_value
    imodintro
    iexists []
    iframe Hcredit
    ipureintro
    rfl

end specification

end

end SampLib.RecycledSamples
