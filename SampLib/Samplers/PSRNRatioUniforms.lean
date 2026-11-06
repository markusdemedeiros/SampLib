import SampLib.LatentUniformRepresentation
import SampLib.LatentProduct
import SampLib.LatentRepresentedProduct
import SampLib.LatentRepresentedDivision
import Samplers.PSRN.Uniform

/-! # The ratio of two independent deferred uniforms

`newRatioUniforms` allocates uniforms `a` and `b` and returns `a / b`. Both caches live
in one product world. The denominator has no atom at zero, and posterior absolute
continuity preserves this fact through every later reciprocal read.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNRatioUniforms

noncomputable section

open LatentReal

abbrev U := LatentUniform.model

abbrev numerator : Model (ℝ × ℝ) (List Bool × List Bool) := ProductModel.left U U

abbrev denominator : Model (ℝ × ℝ) (List Bool × List Bool) := ProductModel.right U U

abbrev numeratorRepresentation : Representation numerator :=
  Representation.productLeft U U LatentUniform.representation

abbrev denominatorRepresentation : Representation denominator :=
  Representation.productRight U U LatentUniform.representation

abbrev model : Model (ℝ × ℝ) (List Bool × List Bool) :=
  RepresentedDivision.model numerator denominator (ProductModel.sameWorld U U)
    denominatorRepresentation

abbrev representation : Representation model :=
  RepresentedDivision.representation numerator denominator (ProductModel.sameWorld U U)
    numeratorRepresentation denominatorRepresentation

/-- The quotient is a view of the product world of both uniforms. -/
theorem sameWorld : numerator.SameWorld model :=
  RepresentedDivision.sameWorld _ _ (ProductModel.sameWorld U U) denominatorRepresentation

abbrev initial : List Bool × List Bool := ([], [])

section mathematics

open MeasureTheory

/-- The output law is the quotient of two independent unit uniforms. -/
theorem initial_law : model.law initial =
    (DyadicPosterior.unitLaw.prod DyadicPosterior.unitLaw).map (fun z : ℝ × ℝ => z.1 / z.2) := by
  change ((DyadicPosterior.law []).prod (DyadicPosterior.law [])).map model.value = _
  rw [DyadicPosterior.law_nil]
  congr 1
  funext z
  rw [RepresentedDivision.value_eq]
  rfl

/-- The denominator vanishes only on a null set of every product posterior. -/
theorem nonzero (s : List Bool × List Bool) : RepresentedReciprocalView.Nonzero denominator s :=
  (Measure.quasiMeasurePreserving_snd (μ := DyadicPosterior.law s.1)
    (ν := DyadicPosterior.law s.2)).ae ((DyadicPosterior.law s.2).ae_ne 0)

end mathematics

namespace Program

private instance divide_closed {rT : Type} : ClosedExp (Occil.PSRN.divide : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private instance uniform_closed {rT : Type} : ClosedExp (Occil.PSRN.newUniform : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

/-- The source body after its unit argument: two allocations, then the quotient closure. -/
def body {rT : Type} : Exp rT :=
  .app (.lam (.app (.lam pl(&Occil.PSRN.divide {Exp.bvar 1} {Exp.bvar 0}))
      pl(&Occil.PSRN.newUniform #())))
    pl(&Occil.PSRN.newUniform #())

theorem source_eq {rT : Type} : (Occil.PSRN.newRatioUniforms : Exp rT) = .lam body := by
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
    tglWp E Program.body Φ ⊢ tglWp E pl(&Occil.PSRN.newRatioUniforms #()) Φ := by
  iintro H
  rw [Program.source_eq]
  ieval (change _ ⊢ tglWp E (Ectx.fill [] (.app (.lam Program.body) Val.unit.fst)) Φ)
  iapply twp_beta E [] Program.body Val.unit Program.source_lc Φ
  isimp only [Ectx.fill_nil, Exp.open', ← Exp.open_lc 0 Val.unit.fst Program.body Program.body_lc]
  iexact H

/-- The returned quotient closure owns both uniform caches once each. -/
def owns (v : Val rT) (s : List Bool × List Bool) : IProp GF :=
  iprop(∃ a b : Val rT,
    ViewOwns (RepresentedDivision.value a b)
      (withInvariant (RepresentedReciprocalView.Nonzero denominator)
        (Product.owns LatentUniform.owns LatentUniform.owns a b)) v s)

/-- Every read observes both components under the one joint product credit. -/
theorem representedOracleSpec (E : CoPset) :
    IsRepresentedOracleSpec (GF := GF) E model representation owns where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [owns] at Hstate
    icases Hstate with ⟨%a, %b, Hstate⟩
    have hquotient := RepresentedDivision.viewSpec E numerator denominator
      (ProductModel.sameWorld U U) numeratorRepresentation denominatorRepresentation
      (Product.owns LatentUniform.owns LatentUniform.owns a b) a b
      (Product.left_representedViewSpec E U U LatentUniform.representation _ _
        (LatentUniform.representedOracleSpec (rT := rT) (GF := GF) E) a b)
      (Product.right_representedViewSpec E U U LatentUniform.representation _ _
        (LatentUniform.representedOracleSpec (rT := rT) (GF := GF) E) a b)
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨%hv, Hstate⟩
    subst v
    iapply hquotient.wp s n F hF _ $$ Hstate Hcredit
    iintro %t %I %hI Hstate Hcredit
    iexists t, I
    isplitl []
    · ipureintro
      exact ⟨rfl, hI⟩
    iframe Hcredit
    isimp only [owns]
    iexists a, b
    isimp only [ViewOwns]
    iframe Hstate

/-- The unchanged source allocates two uniforms and captures their quotient lazily. -/
theorem newRatioUniforms_representedDistSpec (E : CoPset) :
    IsRepresentedDistSpec (GF := GF) E pl(&Occil.PSRN.newRatioUniforms #())
      model representation initial owns where
  oracle := representedOracleSpec E
  spec F hF := by
    iintro Hcredit
    isimp only [sameWorld.posterior_eq, ProductModel.left,
      ProductModel.expectation_left U U initial F hF] at Hcredit
    iapply twp_open E _
    unfold Program.body
    twp_bind pl(&Occil.PSRN.newUniform #())
    iapply ((LatentUniform.newUniform_representedDistSpec E).toIsLatentPayloadSpec.wp
      (ProductModel.leftCredit U [] F) (ProductModel.measurable_leftCredit U [] hF) _)
      $$ Hcredit
    iintro %a %p %hp Ha Hcredit
    twp_pure
    simp only [ClosedExp.openRec]
    twp_bind pl(&Occil.PSRN.newUniform #())
    isimp only [← ProductModel.expectation_left U U (p, []) F hF,
      ProductModel.expectation_right U U (p, []) F hF] at Hcredit
    iapply ((LatentUniform.newUniform_representedDistSpec E).toIsLatentPayloadSpec.wp
      (ProductModel.rightCredit U p F) (ProductModel.measurable_rightCredit U p hF) _)
      $$ Hcredit
    iintro %b %q %hq Hb Hcredit
    isimp only [← ProductModel.expectation_right U U (p, q) F hF] at Hcredit
    twp_pure
    simp only [ClosedExp.openRec]
    iapply tglWp_wand
    isplitl [Ha Hb]
    · iapply RepresentedDivision.twp_constructor E denominator
        (Product.owns LatentUniform.owns LatentUniform.owns a b) a b (p, q)
      isimp only [withInvariant, Product.owns]
      iframe Ha Hb
      ipureintro
      exact nonzero (p, q)
    iintro %v Hstate
    iexists (p, q)
    isimp only [sameWorld.posterior_eq, ProductModel.left]
    iframe Hcredit
    isplitl []
    · ipureintro
      exact (sameWorld.refines_iff _ _).mpr ⟨hp, hq⟩
    isimp only [owns]
    iexists a, b
    iexact Hstate

/-- Standard latent-law interface, including arbitrary future shared observations. -/
theorem newRatioUniforms_latentDistSpec (E : CoPset) :
    IsLatentDistSpec (GF := GF) E pl(&Occil.PSRN.newRatioUniforms #()) model initial owns :=
  (newRatioUniforms_representedDistSpec E).forget

end specification

end

end SampLib.PSRNRatioUniforms
