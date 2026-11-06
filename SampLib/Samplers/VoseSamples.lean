import SampLib.VoseTable
import SampLib.Syntax.Aliases
import SampLib.ListOperations

/-! # Independent categorical samples from a freshly constructed Vose table -/

open ProbLang MeasureTheory
open scoped ENNReal

namespace SampLib.VoseSamples

noncomputable section

/-- The independent categorical vector, decoded as a list in sampling order. -/
def law (ws : List ℕ) (count : ℕ) : Measure (List ℕ) :=
  (SampleWithReplacement.law (WeightedChoice.law ws) count).map List.ofFn

instance (ws : List ℕ) [NeZero ws.sum] (count : ℕ) : IsProbabilityMeasure (law ws count) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

@[simp] theorem law_zero (ws : List ℕ) : law ws 0 = Measure.dirac [] := by
  simp [law, SampleWithReplacement.law]

/-- Decoding the independent vector preserves arbitrary list continuation credits. -/
theorem expectation (ws : List ℕ) (count : ℕ) (F : List ℕ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ xs, F (List.ofFn xs) ∂SampleWithReplacement.law (WeightedChoice.law ws) count =
      ∫⁻ ys, F ys ∂law ws count := by
  rw [law, lintegral_map hF (measurable_of_countable _)]

private def draw {rT : Type _} [ProbLangℝ rT] (table : Val rT) : Val rT :=
  ⟨.lam pl(&Occil.WeightedVariants.voseDraw &table.fst #()), .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem draw_ownedSpec (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (t : AliasMass.Table ws.length ws.sum)
    (hmass : ∀ i, t.mass i = ws.length * ws.get i) (probability aliases : Loc) :
    IsOwnedDistSpec (rT := rT) (GF := GF) E
      (AliasTable.owns (rT := rT) t probability aliases)
      pl(&(draw (AliasTable.value ws.length ws.sum probability aliases)).fst #())
      (WeightedChoice.law ws) (fun i : ℕ => Val.int i) where
  spec F hF := by
    iintro Hinput
    twp_pure
    simp only [AliasSyntax.voseDraw_openRec]
    iapply (AliasTable.voseDraw_ownedDistSpec E ws (NeZero.pos ws.sum)
      t hmass probability aliases).spec F hF $$ Hinput

/-- Nonnegative counts, including zero, with nonnegative weights of positive total. -/
theorem voseSamples_distSpec (E : CoPset) (ws : List ℕ) [NeZero ws.sum] (count : ℕ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.WeightedVariants.voseSamples
        &(listVal (fun i : ℕ => (Val.int i : Val rT)) ws).fst #int (count : ℤ))
      (law ws count) (fun xs => listVal (fun i : ℕ => Val.int i) xs) where
  spec F hF := by
    iintro Hcredit
    isimp only [← expectation ws count F hF] at Hcredit
    iterate 4 twp_pure
    simp only [AliasSyntax.voseTable_openRec, AliasSyntax.voseTable_closeRec,
      AliasSyntax.voseDraw_openRec, AliasSyntax.voseDraw_closeRec,
      ListOperations.repeatSample_openRec, ListOperations.repeatSample_closeRec]
    twp_bind pl(&Occil.WeightedVariants.voseTable
      &(listVal (fun i : ℕ => (Val.int i : Val rT)) ws).fst)
    iapply tglWp_wand
    isplitl []
    · iapply VoseTable.twp_voseTable E ws (NeZero.pos ws.sum)
    iintro %v ⟨%t, %probability, %aliases, %hdata, Htable⟩
    rcases hdata with ⟨hv, hmass⟩
    subst v
    twp_pure
    simp only [AliasSyntax.voseDraw_openRec, ListOperations.repeatSample_openRec]
    have hrepeat := repeatSample_ownedDistSpec (GF := GF) E
      (AliasTable.owns (rT := rT) t probability aliases) (WeightedChoice.law ws)
      (fun i : ℕ => (Val.int i : Val rT))
      (draw (AliasTable.value ws.length ws.sum probability aliases))
      (draw_ownedSpec E ws t hmass probability aliases) count
    simp only [draw] at hrepeat
    iapply tglWp_wand
    isplitl [Htable Hcredit]
    · iapply hrepeat.spec (fun xs => F (List.ofFn xs)) (measurable_of_countable _)
      iframe Htable Hcredit
    iintro %v ⟨%xs, %hv, Htable, Hcredit⟩
    iexists List.ofFn xs
    iframe %hv Hcredit

end specification

end

end SampLib.VoseSamples
