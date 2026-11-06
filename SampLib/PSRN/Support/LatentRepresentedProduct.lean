import SampLib.PSRN.Support.LatentRepresentedViews
import SampLib.PSRN.Support.LatentProduct

/-! # Represented coordinates of independently constructed latent worlds

Each projection certifies its actual interval while retaining both component
resources and the complete product-posterior continuation credit.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

namespace Representation

variable {Ω₁ Ω₂ S₁ S₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

def productLeft (L : Model Ω₁ S₁) (R : Model Ω₂ S₂) (left : Representation L) :
    Representation (ProductModel.left L R) where
  interval n z := left.interval n z.1
  measurable_lower n := (left.measurable_lower n).comp measurable_fst
  measurable_upper n := (left.measurable_upper n).comp measurable_fst
  measurable_denominator n := (left.measurable_denominator n).comp measurable_fst
  approximates s := (MeasureTheory.Measure.quasiMeasurePreserving_fst
    (μ := L.posterior s.1) (ν := R.posterior s.2)).ae (left.approximates s.1)

def productRight (L : Model Ω₁ S₁) (R : Model Ω₂ S₂) (right : Representation R) :
    Representation (ProductModel.right L R) where
  interval n z := right.interval n z.2
  measurable_lower n := (right.measurable_lower n).comp measurable_snd
  measurable_upper n := (right.measurable_upper n).comp measurable_snd
  measurable_denominator n := (right.measurable_denominator n).comp measurable_snd
  approximates s := (MeasureTheory.Measure.quasiMeasurePreserving_snd
    (μ := L.posterior s.1) (ν := R.posterior s.2)).ae (right.approximates s.2)

theorem observed_productLeft (L : Model Ω₁ S₁) (R : Model Ω₂ S₂) (left : Representation L)
    {s : S₁} (t : S₂) {n : ℕ} {I : RationalInterval} (hI : left.Observed s n I) :
    (productLeft L R left).Observed (s, t) n I :=
  (MeasureTheory.Measure.quasiMeasurePreserving_fst
    (μ := L.posterior s) (ν := R.posterior t)).ae hI

theorem observed_productRight (L : Model Ω₁ S₁) (R : Model Ω₂ S₂) (right : Representation R)
    (s : S₁) {t : S₂} {n : ℕ} {I : RationalInterval} (hI : right.Observed t n I) :
    (productRight L R right).Observed (s, t) n I :=
  (MeasureTheory.Measure.quasiMeasurePreserving_snd
    (μ := L.posterior s) (ν := R.posterior t)).ae hI

end Representation

namespace Product

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω₁ Ω₂ S₁ S₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
local bi (IProp GF)

/-- Observing the first component retains the second resource and its latent dependence in `F`. -/
theorem left_representedViewSpec (E : CoPset) (L : Model Ω₁ S₁) (R : Model Ω₂ S₂)
    (repr : Representation L) (OL : Val rT → S₁ → IProp GF) (OR : Val rT → S₂ → IProp GF)
    (hL : IsRepresentedOracleSpec E L repr OL) (left right : Val rT) :
    IsRepresentedViewSpec E (ProductModel.left L R) (Representation.productLeft L R repr)
      (owns OL OR left right) left where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns, owns] at Hstate
    icases Hstate with ⟨%hv, Hleft, Hright⟩
    subst v
    isimp only [ProductModel.left, ProductModel.expectation_left L R s F hF] at Hcredit
    iapply (IsRepresentedOracleSpec.wp hL left s.1 n (ProductModel.leftCredit R s.2 F)
      (ProductModel.measurable_leftCredit R s.2 hF) _) $$ Hleft Hcredit
    iintro %t %I %hI Hleft Hcredit
    isimp only [← ProductModel.expectation_left L R (t, s.2) F hF] at Hcredit
    iexists (t, s.2), I
    isplitl []
    · ipureintro
      exact ⟨rfl, ⟨hI.1, R.refines_refl _⟩,
        ProductModel.encloses_left L R s.2 hI.2.1,
        Representation.observed_productLeft L R repr s.2 hI.2.2⟩
    isimp only [ViewOwns, owns, ProductModel.left]
    iframe Hleft Hright Hcredit

/-- The second component uses the other Tonelli order with the same whole-world credit. -/
theorem right_representedViewSpec (E : CoPset) (L : Model Ω₁ S₁) (R : Model Ω₂ S₂)
    (repr : Representation R) (OL : Val rT → S₁ → IProp GF) (OR : Val rT → S₂ → IProp GF)
    (hR : IsRepresentedOracleSpec E R repr OR) (left right : Val rT) :
    IsRepresentedViewSpec E (ProductModel.right L R) (Representation.productRight L R repr)
      (owns OL OR left right) right where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns, owns] at Hstate
    icases Hstate with ⟨%hv, Hleft, Hright⟩
    subst v
    isimp only [ProductModel.right, ProductModel.left,
      ProductModel.expectation_right L R s F hF] at Hcredit
    iapply (IsRepresentedOracleSpec.wp hR right s.2 n (ProductModel.rightCredit L s.1 F)
      (ProductModel.measurable_rightCredit L s.1 hF) _) $$ Hright Hcredit
    iintro %t %I %hI Hright Hcredit
    isimp only [← ProductModel.expectation_right L R (s.1, t) F hF] at Hcredit
    iexists (s.1, t), I
    isplitl []
    · ipureintro
      exact ⟨rfl, ⟨L.refines_refl _, hI.1⟩,
        ProductModel.encloses_right L R s.1 hI.2.1,
        Representation.observed_productRight L R repr s.1 hI.2.2⟩
    isimp only [ViewOwns, owns, ProductModel.right, ProductModel.left]
    iframe Hleft Hright Hcredit

end specification

end Product

end

end SampLib.LatentReal
