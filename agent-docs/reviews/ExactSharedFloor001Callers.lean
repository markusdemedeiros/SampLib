import SampLib.PSRN.Support.PSRNFloor
import SampLib.PSRN.Support.LatentRational

open ProbLang
open scoped ENNReal

namespace ReviewSharedFloor001

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib SampLib.LatentReal

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

theorem framed (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (owns : Val rT → S → IProp GF) (horacle : IsOracleSpec E D owns)
    (source : Val rT) (scale : ℤ) (hscale : 0 < scale) (s : S)
    (hgrid : Floor.AvoidsGrid D scale s) (G : ℤ → Ω → ℝ≥0∞)
    (hG : ∀ z, Measurable (G z)) (R : IProp GF) :
    iprop(owns source s ∗ ↯ (∫⁻ x, Floor.outputCredit D scale G x ∂D.posterior s) ∗ R) ⊢
      tglWp E pl(&Occil.PSRN.floorScaled &source.fst #scale)
        (fun v : Val rT => iprop(Floor.post D scale (owns source) s G v ∗ R)) := by
  iintro ⟨Hstate, Hcredit, HR⟩
  iapply tglWp_wand
  isplitl [Hstate Hcredit]
  · iapply Floor.twp_floorScaled E D hD owns horacle source scale hscale s hgrid G hG
    iframe Hstate Hcredit
  iintro %v Hpost
  iframe Hpost HR

private theorem negative_avoids : Floor.AvoidsGrid (LatentRational.model (-1) 2) 3 () := by
  apply Filter.Eventually.of_forall
  intro x
  norm_num [Floor.output, LatentRational.model]

example : Floor.output (LatentRational.model (-1) 2) 3 () = -2 := by
  norm_num [Floor.output, LatentRational.model]

/-- Atoms away from the grid are permitted; neither continuity nor positivity is required. -/
example (E : CoPset) (G : ℤ → Unit → ℝ≥0∞) (R : IProp GF) :=
  framed E (LatentRational.model (-1) 2) (fun _ => measurable_const)
    (LatentRational.owns (-1) 2) (LatentRational.oracleSpec E (-1) 2 (by decide))
    (LatentRational.value (-1) 2) 3 (by decide) () negative_avoids
    G (fun _ => measurable_of_countable _) R

example (E : CoPset) (R : IProp GF) :=
  framed E (LatentRational.model (-1) 2) (fun _ => measurable_const)
    (LatentRational.owns (-1) 2) (LatentRational.oracleSpec E (-1) 2 (by decide))
    (LatentRational.value (-1) 2) 3 (by decide) () negative_avoids
    (fun _ _ => ∞) (fun _ => measurable_const) R

/-- Infinite credit on every impossible integer still gives zero expected input credit. -/
example : (∫⁻ x, Floor.outputCredit (LatentRational.model (-1) 2) 3
    (fun z _ => if z = -2 then 0 else ∞) x ∂(LatentRational.model (-1) 2).posterior ()) = 0 := by
  norm_num [Floor.outputCredit, Floor.output, LatentRational.model]

/-- Grid atoms fall outside this sufficient domain, even when another direct rule could work. -/
example : ¬Floor.AvoidsGrid (LatentRational.model 1 1) 1 () := by
  simp [Floor.AvoidsGrid, Floor.output, LatentRational.model]

#print axioms SampLib.LatentReal.Floor.twp_floorScaled_view
#print axioms SampLib.LatentReal.Floor.twp_floorScaled
#print axioms SampLib.LatentReal.Floor.expectation_preservation
#print axioms framed
#print axioms negative_avoids

end
end ReviewSharedFloor001
