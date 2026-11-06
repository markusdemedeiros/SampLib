import SampLib.Samplers.PSRNPowerUniform

/-! # The reciprocal of a rational power of one deferred uniform

`newReciprocalPowerUniform a b` calls the verified `newPowerUniform a b` and takes the
actual adaptive reciprocal of its oracle. Every branch of the power is positive almost
surely, so each reciprocal read terminates, and the output is `u ^ (-a / b)`.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNReciprocalPowerUniform

noncomputable section

open LatentReal

abbrev model (a : ℤ) (b : ℕ) : Model ℝ (List Bool) :=
  RepresentedReciprocal.model (PSRNPowerUniform.model a b) (PSRNPowerUniform.representation a b)

abbrev representation (a : ℤ) (b : ℕ) : Representation (model a b) :=
  RepresentedReciprocal.representation (PSRNPowerUniform.model a b)
    (PSRNPowerUniform.representation a b)

theorem sameWorld (a : ℤ) (b : ℕ) : PSRNPowerUniform.U.SameWorld (model a b) :=
  (PSRNPowerUniform.sameWorld a b).trans (RepresentedReciprocal.sameWorld _ _)

section mathematics

open MeasureTheory

/-- The output law is the image of the unit uniform under `u ↦ u ^ (-a / b)`. -/
theorem initial_law (a : ℤ) {b : ℕ} (hb : 0 < b) :
    (model a b).law [] = DyadicPosterior.unitLaw.map (fun u => u ^ (-(a : ℝ) / b)) := by
  rw [Model.law, (sameWorld a b).posterior_eq]
  change (DyadicPosterior.law []).map _ = _
  rw [DyadicPosterior.law_nil]
  apply Measure.map_congr
  have hpos := PSRNPowerUniform.ae_pos []
  rw [DyadicPosterior.law_nil] at hpos
  filter_upwards [hpos] with u hu
  change 1 / (PSRNPowerUniform.model a b).value u = _
  rw [PSRNPowerUniform.model_value a hb hu, one_div, ← Real.rpow_neg hu.le, neg_div]

end mathematics

private instance power_closed {rT : Type} :
    ClosedExp (Occil.PSRN.newPowerUniform : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private instance reciprocal_closed {rT : Type} : ClosedExp (Occil.PSRN.reciprocal : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The reciprocal closure retains the power oracle and its one uniform cache. -/
abbrev owns (a : ℤ) (b : ℕ) : Val rT → List Bool → IProp GF :=
  RepresentedReciprocal.owns (PSRNPowerUniform.model a b) (PSRNPowerUniform.owns a b)

/-- The unchanged source inverts the verified power oracle without observing it. -/
theorem newReciprocalPowerUniform_representedDistSpec (E : CoPset) (a : ℤ) (b : ℕ)
    (hb : 0 < b) :
    IsRepresentedDistSpec (GF := GF) E
      pl(&Occil.PSRN.newReciprocalPowerUniform #a #int (b : ℤ) #())
      (model a b) (representation a b) [] (owns a b) where
  oracle := RepresentedReciprocal.oracleSpec E _ _ _
    (PSRNPowerUniform.representedOracleSpec E a b hb)
  spec F hF := by
    iintro Hcredit
    iterate 3 twp_pure
    simp only [ClosedExp.openRec, ClosedExp.closeRec]
    twp_bind pl(&Occil.PSRN.newPowerUniform #a #int (b : ℤ) #())
    isimp only [(RepresentedReciprocal.sameWorld (PSRNPowerUniform.model a b)
      (PSRNPowerUniform.representation a b)).posterior_eq] at Hcredit
    iapply ((PSRNPowerUniform.newPowerUniform_latentDistSpec E a b hb).wp F hF _) $$ Hcredit
    iintro %power %p %hp Hstate Hcredit
    simp only [Exp.ofVal]
    iapply tglWp_wand
    isplitl [Hstate Hcredit]
    · iapply RepresentedReciprocal.twp_reciprocal E _ (PSRNPowerUniform.representation a b)
        (PSRNPowerUniform.owns a b) power p (PSRNPowerUniform.model_nonzero a hb p) F
      iframe Hstate Hcredit
    iintro %v ⟨Hstate, Hcredit⟩
    iexists p
    iframe Hstate Hcredit
    ipureintro
    exact hp

/-- Standard latent-law interface, including arbitrary future shared observations. -/
theorem newReciprocalPowerUniform_latentDistSpec (E : CoPset) (a : ℤ) (b : ℕ) (hb : 0 < b) :
    IsLatentDistSpec (GF := GF) E
      pl(&Occil.PSRN.newReciprocalPowerUniform #a #int (b : ℤ) #())
      (model a b) [] (owns a b) :=
  (newReciprocalPowerUniform_representedDistSpec E a b hb).forget

end specification

end

end SampLib.PSRNReciprocalPowerUniform
