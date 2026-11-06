import SampLib.PSRN.PSRNExponentialRational
import SampLib.PSRN.Support.LatentRoot
import SampLib.PSRN.Support.LatentRootLaw
import SampLib.PSRN.Support.LatentRealConstructors
import Samplers.PSRN.Distributions

/-! # Rayleigh sampling by an exponential draw and an exact square root -/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNRayleigh

noncomputable section

open LatentReal

private abbrev sourceRate : ℝ := ((1 : ℤ) : ℝ) / (1 : ℤ)

private def sourceModel := LatentExponential.model sourceRate (by norm_num [sourceRate])

def initial := LatentExponential.initial sourceRate

private def scaledModel := sourceModel.scale 2

/-- The observable retains the same exponential latent world through both transformations. -/
def model := scaledModel.nthRoot 2

private theorem source_law : sourceModel.law initial = ProbabilityTheory.expMeasure 1 := by
  simpa only [sourceModel, initial, sourceRate, Int.cast_one, div_one] using
    LatentExponential.initial_law sourceRate (by norm_num [sourceRate])

/-- The represented output has the standard unit-scale Rayleigh law. -/
theorem model_law : model.law initial = law := Model.rayleigh_law sourceModel initial source_law

private theorem source_measurable_error : sourceModel.MeasurableError :=
  LatentExponential.measurable_error sourceRate (by norm_num [sourceRate])

private theorem scaled_measurable_error : scaledModel.MeasurableError :=
  fun n => (source_measurable_error n).mul_const _

private theorem admissible : Root.Admissible scaledModel 2 initial :=
  Model.rayleigh_admissible sourceModel initial source_law

private instance exponential_closed {rT : Type} :
    ClosedExp (Occil.PSRN.newExponential : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private instance scale_closed {rT : Type} : ClosedExp (Occil.PSRN.scaleRational : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private instance root_closed {rT : Type} : ClosedExp (Occil.PSRN.root : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The square-root closure retains its original exponential oracle and physical cache. -/
abbrev owns := Root.owns scaledModel 2
  (scaleRationalOwns (PSRNExponential.rationalOwns (rT := rT) (GF := GF) 1 1) 2 1)

/-- The actual sampler and every later observation preserve arbitrary joint latent credit. -/
theorem newRayleigh_representedDistSpec (E : CoPset) :
    IsRepresentedDistSpec (rT := rT) (GF := GF) E pl(&Occil.PSRN.newRayleigh #())
      model model.dyadicRepresentation initial owns := by
  have hexponential : IsLatentDistSpec (rT := rT) (GF := GF) E
      pl(&Occil.PSRN.newExponential #1 #1 #())
      sourceModel initial (PSRNExponential.rationalOwns 1 1) :=
    PSRNExponential.newExponential_latentDistSpec E 1 1 (by decide) (by decide)
  have hscaled : IsOracleSpec (rT := rT) (GF := GF) E scaledModel
      (scaleRationalOwns (PSRNExponential.rationalOwns 1 1) 2 1) := by
    simpa only [scaledModel, Int.cast_ofNat, Int.cast_one, div_one] using
      scaleRational_oracleSpec E sourceModel _ hexponential.oracle 2 1 (by decide)
  refine {
    oracle := Root.representedOracleSpec E scaledModel scaled_measurable_error
      _ hscaled 2 (by decide)
    spec := ?_
  }
  intro F hF
  iintro Hcredit
  isimp only [model, Model.nthRoot, scaledModel, Model.scale] at Hcredit
  twp_pure
  isimp only [ClosedExp.openRec, ClosedExp.closeRec]
  twp_bind pl(&Occil.PSRN.newExponential #1 #1 #())
  iapply hexponential.wp F hF _ $$ Hcredit
  iintro %source %t %ht Hstate Hcredit
  twp_pure
  isimp only [ClosedExp.openRec, ClosedExp.closeRec]
  twp_bind pl(&Occil.PSRN.scaleRational &source.fst #2 #1)
  iapply tglWp_wand
  isplitl [Hstate]
  · iapply twp_scaleRational E (PSRNExponential.rationalOwns 1 1) source t 2 1 (by decide)
      $$ Hstate
  iintro %scaled Hstate
  isimp only [Exp.ofVal]
  iapply tglWp_wand
  isplitl [Hstate]
  · iapply Root.Program.twp_root E scaled 2 (by decide) _ t $$ Hstate
  iintro %v Hstate
  isimp only [ViewOwns] at Hstate
  icases Hstate with ⟨%hv, Hstate⟩
  subst v
  iexists t
  isplit
  · ipureintro
    exact ht
  isplitl [Hstate]
  · isimp only [owns, Root.owns]
    iexists scaled
    iframe Hstate
    ipureintro
    exact ⟨rfl, admissible.refines ht⟩
  isimp only [model, Model.nthRoot, scaledModel, Model.scale]
  iframe Hcredit

/-- Ordinary latent-distribution form for callers that do not need exact interval formatting. -/
theorem newRayleigh_latentDistSpec (E : CoPset) :
    IsLatentDistSpec (rT := rT) (GF := GF) E pl(&Occil.PSRN.newRayleigh #()) model initial owns :=
  (newRayleigh_representedDistSpec E).forget

end specification

end

end SampLib.PSRNRayleigh
