import SampLib.PSRN.Laws.UniformOdds
import SampLib.PSRN.Support.Represented.Uniform
import SampLib.PSRN.Support.Represented.Complement
import SampLib.PSRN.Support.Represented.Division
import Samplers.PSRN.Uniform

/-! # The odds of one shared deferred uniform

`newOddsUniform` allocates one uniform `u` and returns `u / (1 - u)`. Numerator and
denominator read the same cache. The denominator has no atom at zero, and posterior
absolute continuity preserves this fact through every later reciprocal read.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNOddsUniform

noncomputable section

open LatentReal

/-- The complement `1 - u`, as the actual source builds it: `1 + (-u)`. -/
abbrev complement : Model ℝ (List Bool) :=
  LatentUniform.model.negate.translate (((1 : ℤ) : ℝ) / (1 : ℤ))

abbrev complementRepresentation : Representation complement :=
  Representation.translate _ (Representation.negate _ LatentUniform.representation) 1 1
    (by decide)

theorem complement_sameWorld : LatentUniform.model.SameWorld complement :=
  ⟨fun _ => rfl, fun _ _ => Iff.rfl⟩

abbrev model : Model ℝ (List Bool) :=
  RepresentedDivision.model LatentUniform.model complement complement_sameWorld
    complementRepresentation

abbrev representation : Representation model :=
  RepresentedDivision.representation LatentUniform.model complement complement_sameWorld
    LatentUniform.representation complementRepresentation

/-- The quotient is a view of the uniform's own posterior world. -/
theorem sameWorld : LatentUniform.model.SameWorld model :=
  RepresentedDivision.sameWorld _ _ complement_sameWorld complementRepresentation

section mathematics

open MeasureTheory

theorem model_value (u : ℝ) : model.value u = UniformOdds.transform u := by
  rw [RepresentedDivision.value_eq]
  simp [UniformOdds.transform, complement, Model.translate, Model.negate, LatentUniform.model,
    sub_eq_add_neg]

/-- The normalized output law is that of the odds of a unit uniform. -/
theorem initial_law : model.law [] = UniformOdds.law := by
  change (DyadicPosterior.law []).map model.value = _
  rw [DyadicPosterior.law_nil, funext model_value]
  rfl

/-- The denominator `1 - u` vanishes only on a null set of any posterior. -/
theorem nonzero (p : List Bool) : RepresentedReciprocalView.Nonzero complement p := by
  filter_upwards [(DyadicPosterior.law p).ae_ne 1] with u hu
  change ((1 : ℤ) : ℝ) / (1 : ℤ) + -u ≠ 0
  intro h
  exact hu (by norm_num at h; linarith)

end mathematics

namespace Program

private instance divide_closed {rT : Type} : ClosedExp (Occil.PSRN.divide : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private instance subtract_closed {rT : Type} : ClosedExp (Occil.PSRN.subtract : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private instance rational_closed {rT : Type} : ClosedExp (Occil.PSRN.rational : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

/-- The source body after its unit argument: allocate, then capture the quotient. -/
def body {rT : Type} : Exp rT :=
  .app (.lam pl(&Occil.PSRN.divide {Exp.bvar 0}
      (&Occil.PSRN.subtract (&Occil.PSRN.rational #1 #1) {Exp.bvar 0})))
    pl(&Occil.PSRN.newUniform #())

theorem source_eq {rT : Type} : (Occil.PSRN.newOddsUniform : Exp rT) = .lam body := by
  kernel_rfl

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

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_open (E : CoPset) (Φ : Val rT → IProp GF) :
    tglWp E Program.body Φ ⊢ tglWp E pl(&Occil.PSRN.newOddsUniform #()) Φ := by
  iintro H
  rw [Program.source_eq]
  ieval (change _ ⊢ tglWp E (Ectx.fill [] (.app (.lam Program.body) Val.unit.fst)) Φ)
  iapply twp_beta E [] Program.body Val.unit Program.source_lc Φ
  isimp only [Ectx.fill_nil, Exp.open', ← Exp.open_lc 0 Val.unit.fst Program.body Program.body_lc]
  iexact H

/-- The returned quotient closure owns exactly one uniform cache. -/
def owns (v : Val rT) (p : List Bool) : IProp GF :=
  iprop(∃ source : Val rT,
    ViewOwns (RepresentedDivision.value source (subtractFromPointVal source 1 1))
      (withInvariant (RepresentedReciprocalView.Nonzero complement)
        (LatentUniform.owns source)) v p)

/-- Every read observes numerator and complement of the same cached uniform. -/
theorem representedOracleSpec (E : CoPset) :
    IsRepresentedOracleSpec (GF := GF) E model representation owns where
  observe v p n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [owns] at Hstate
    icases Hstate with ⟨%source, Hstate⟩
    have hsource := (LatentUniform.representedOracleSpec (rT := rT) (GF := GF) E).viewSpec
      source
    have hquotient := RepresentedDivision.viewSpec E LatentUniform.model complement
      complement_sameWorld LatentUniform.representation complementRepresentation
      (LatentUniform.owns source) source (subtractFromPointVal source 1 1) hsource
      (represented_subtractFromPoint_viewSpec E LatentUniform.model
        LatentUniform.representation _ source hsource 1 1 (by decide))
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨%hv, Hstate⟩
    subst v
    iapply hquotient.wp p n F hF _ $$ Hstate Hcredit
    iintro %t %I %hI Hstate Hcredit
    iexists t, I
    isplitl []
    · ipureintro
      exact ⟨rfl, hI⟩
    iframe Hcredit
    isimp only [owns]
    iexists source
    isimp only [ViewOwns]
    iframe Hstate

/-- The unchanged source allocates one uniform and captures `u / (1 - u)` lazily. -/
theorem newOddsUniform_representedDistSpec (E : CoPset) :
    IsRepresentedDistSpec (GF := GF) E pl(&Occil.PSRN.newOddsUniform #())
      model representation [] owns where
  oracle := representedOracleSpec E
  spec F hF := by
    iintro Hcredit
    isimp only [sameWorld.posterior_eq] at Hcredit
    iapply twp_open E _
    unfold Program.body
    twp_bind pl(&Occil.PSRN.newUniform #())
    iapply ((LatentUniform.newUniform_representedDistSpec E).toIsLatentPayloadSpec.wp F hF _)
      $$ Hcredit
    iintro %source %p %hp Hstate Hcredit
    twp_pure
    simp only [ClosedExp.openRec]
    twp_bind pl(&Occil.PSRN.subtract (&Occil.PSRN.rational #1 #1) &source.fst)
    iapply tglWp_wand
    isplitl [Hstate]
    · iapply twp_subtractFromPoint E source (LatentUniform.owns source) p 1 1 (by decide)
        $$ Hstate
    iintro %denominator Hstate
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨%hd, Hstate⟩
    subst denominator
    simp only [Exp.ofVal]
    iapply tglWp_wand
    isplitl [Hstate]
    · iapply RepresentedDivision.twp_constructor E complement (LatentUniform.owns source) source
        (subtractFromPointVal source 1 1) p
      isimp only [withInvariant]
      iframe Hstate
      ipureintro
      exact nonzero p
    iintro %v Hstate
    iexists p
    isimp only [sameWorld.posterior_eq]
    iframe Hcredit
    isplitl []
    · ipureintro
      exact (sameWorld.refines_iff _ _).mpr hp
    isimp only [owns]
    iexists source
    iexact Hstate

/-- Standard latent-law interface, including arbitrary future shared observations. -/
theorem newOddsUniform_latentDistSpec (E : CoPset) :
    IsLatentDistSpec (GF := GF) E pl(&Occil.PSRN.newOddsUniform #()) model [] owns :=
  (newOddsUniform_representedDistSpec E).forget

end specification

end

end SampLib.PSRNOddsUniform
