import SampLib.Samplers.RndIntRange
import SampLib.DistributionMapSupported

/-! # Inclusive uniform intervals with natural offsets

The program returns an integer, while callers reason about the offset from the
lower endpoint. Transporting the existing interval specification preserves its
arbitrary continuation credits.
-/

open ProbLang

namespace SampLib.InclusiveOffset

noncomputable section

section mathematics

open MeasureTheory

private theorem ae_lower (lo hi : ℤ) : ∀ᵐ z ∂RndIntRange.law lo hi, lo ≤ z := by
  rw [RndIntRange.law]
  apply (ae_map_iff (measurable_of_countable _).aemeasurable (measurableSet_le measurable_const
    measurable_id)).2
  filter_upwards [] with k
  change lo ≤ lo + (k : ℤ)
  omega

private theorem map_offset (lo hi : ℤ) :
    (RndIntRange.law lo hi).map (fun z => (z - lo).toNat) = RndInt.law (hi - lo).toNat := by
  rw [RndIntRange.law, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have h : (fun z : ℤ => (z - lo).toNat) ∘ (fun k : ℕ => lo + (k : ℤ)) = id := by
    funext k
    simp
  rw [h, Measure.map_id]

end mathematics

open Iris TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]

/-- A nonempty integer interval is an inclusive uniform natural offset. -/
theorem rndIntRange_distSpec (E : CoPset) (lo hi : ℤ) (h : lo ≤ hi) :
    IsDistSpec (GF := GF) E pl(&Occil.rndIntRange #lo #hi) (RndInt.law (hi - lo).toNat)
      (fun k => Val.int (lo + (k : ℤ))) := by
  have hs := (RndIntRange.rndIntRange_distSpec (GF := GF) (rT := rT) E lo hi h).map_supported
    (fun z => lo ≤ z) (measurableSet_le measurable_const measurable_id) (ae_lower lo hi)
    (fun z => (z - lo).toNat) (measurable_of_countable _) (fun k => Val.int (lo + (k : ℤ)))
    (by intro z hz; congr 1; omega)
  simpa only [map_offset] using hs

end

end SampLib.InclusiveOffset
