import SampLib.PSRN.Laws.ReciprocalUniform
import SampLib.PSRN.Support.Represented.Uniform
import SampLib.PSRN.Support.Represented.Reciprocal
import Samplers.PSRN.Uniform

/-! # A reciprocal uniform with shared deferred digits

One uniform is allocated, and every reciprocal observation refines that same
cache until its interval excludes zero. The initial uniform has no atom at zero;
posterior absolute continuity preserves this fact through all subsequent reads.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNReciprocalUniform

noncomputable section

open LatentReal

abbrev model := RepresentedReciprocal.model LatentUniform.model LatentUniform.representation

abbrev representation :=
  RepresentedReciprocal.representation LatentUniform.model LatentUniform.representation

/-- The represented output is the inverse of the original unit uniform. -/
theorem initial_law_pushforward :
    model.law [] = DyadicPosterior.unitLaw.map (fun x : ℝ => 1 / x) := by
  change (DyadicPosterior.law []).map (fun x : ℝ => 1 / x) = _
  rw [DyadicPosterior.law_nil]

/-- The normalized output law is the canonical scale-one, shape-one Pareto measure. -/
theorem initial_law : model.law [] = ProbabilityTheory.paretoMeasure 1 1 := by
  rw [initial_law_pushforward]
  exact ReciprocalUniform.law_eq_pareto

/-- Adaptive inverse widths remain measurable functions of the shared latent value. -/
theorem measurable_error : model.MeasurableError :=
  RepresentedReciprocal.measurableError LatentUniform.model LatentUniform.representation

private theorem nonzero (p : List Bool) :
    ∀ᵐ x ∂LatentUniform.model.posterior p, LatentUniform.model.value x ≠ 0 :=
  (DyadicPosterior.law p).ae_ne 0

namespace Program

def body {rT : Type} : Exp rT :=
  .app Occil.PSRN.reciprocal (.app Occil.PSRN.newUniform (.lit .unit))

theorem source_eq {rT : Type} :
    (Occil.PSRN.newReciprocalUniform : Exp rT) = .lam body := by kernel_rfl

theorem body_lc {rT : Type} : (body : Exp rT).IsLocallyClosed := by
  unfold body
  is_lc

theorem source_lc {rT : Type} : (Exp.lam body : Exp rT).IsLocallyClosed := by
  rw [← source_eq]
  is_lc

end Program

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- A reciprocal closure owns the single uniform cache from which it was built. -/
abbrev owns : Val rT → List Bool → IProp GF :=
  RepresentedReciprocal.owns LatentUniform.model LatentUniform.owns

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_open (E : CoPset) (Φ : Val rT → IProp GF) :
    tglWp E Program.body Φ ⊢ tglWp E pl(&Occil.PSRN.newReciprocalUniform #()) Φ := by
  iintro H
  rw [Program.source_eq]
  ieval (change _ ⊢ tglWp E (Ectx.fill [] (.app (.lam Program.body) Val.unit.fst)) Φ)
  iapply twp_beta E [] Program.body Val.unit Program.source_lc Φ
  isimp only [Ectx.fill_nil, Exp.open', ← Exp.open_lc 0 Val.unit.fst Program.body Program.body_lc]
  iexact H

/-- Every read retains the actual adaptive interval and the whole uniform posterior. -/
theorem representedOracleSpec (E : CoPset) :
    LatentReal.IsRepresentedOracleSpec (GF := GF) E model representation owns :=
  RepresentedReciprocal.oracleSpec E LatentUniform.model LatentUniform.representation
    LatentUniform.owns (LatentUniform.representedOracleSpec E)

/-- The unchanged source constructs the reciprocal of one shared uniform draw. -/
theorem newReciprocalUniform_representedDistSpec (E : CoPset) :
    LatentReal.IsRepresentedDistSpec (GF := GF) E pl(&Occil.PSRN.newReciprocalUniform #())
      model representation [] owns where
  oracle := representedOracleSpec E
  spec F hF := by
    iintro Hcredit
    iapply twp_open E _
    twp_bind pl(&Occil.PSRN.newUniform #())
    isimp only [RepresentedReciprocal.model] at Hcredit
    iapply ((LatentUniform.newUniform_representedDistSpec E).toIsLatentPayloadSpec.wp F hF _)
      $$ Hcredit
    iintro %source %p %hp Hstate Hcredit
    isimp only [Exp.ofVal]
    iapply tglWp_wand
    isplitl [Hstate Hcredit]
    · iapply RepresentedReciprocal.twp_reciprocal E LatentUniform.model LatentUniform.representation
        LatentUniform.owns source p (nonzero p) F
      iframe Hstate Hcredit
    iintro %result ⟨Hstate, Hcredit⟩
    iexists p
    iframe Hstate Hcredit
    ipureintro
    exact hp

/-- Standard latent-law interface, including arbitrary future shared observations. -/
theorem newReciprocalUniform_latentDistSpec (E : CoPset) :
    LatentReal.IsLatentDistSpec (GF := GF) E pl(&Occil.PSRN.newReciprocalUniform #())
      model [] owns := (newReciprocalUniform_representedDistSpec E).forget

end specification

end

end SampLib.PSRNReciprocalUniform
