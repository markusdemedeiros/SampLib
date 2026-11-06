import SampLib.LatentProductModel
import SampLib.LatentPayloadSpec

/-! # Constructing and observing independent deferred components

Construction uses Tonelli in each order. After construction, both coordinate
views thread one common physical resource and one full product-posterior credit.
-/

open ProbLang
open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal

namespace SampLib.LatentReal.Product

noncomputable section

/-- Two constructors evaluated left to right, with arbitrary named variables preserved. -/
def code {rT : Type} (left right : Exp rT) : Exp rT :=
  .app (.lam (.app (.lam (.pair (.bvar 1) (.bvar 0))) right)) left

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω₁ Ω₂ S₁ S₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
local bi (IProp GF)

/-- A single common ownership for two independently allocated oracle states. -/
def owns (OL : Val rT → S₁ → IProp GF) (OR : Val rT → S₂ → IProp GF)
    (left right : Val rT) (s : S₁ × S₂) : IProp GF := iprop(OL left s.1 ∗ OR right s.2)

/-- The actual returned pair carries both handles and their common physical state. -/
def pairOwns (OL : Val rT → S₁ → IProp GF) (OR : Val rT → S₂ → IProp GF)
    (v : Val rT) (s : S₁ × S₂) : IProp GF :=
  iprop(∃ (left right : Val rT), ⌜v = Val.pair left right⌝ ∗ owns OL OR left right s)

/-- Reading the first coordinate retains the second oracle and joint continuation. -/
theorem left_viewSpec (E : CoPset) (L : Model Ω₁ S₁) (R : Model Ω₂ S₂)
    (OL : Val rT → S₁ → IProp GF) (OR : Val rT → S₂ → IProp GF)
    (hL : IsOracleSpec E L OL) (left right : Val rT) :
    IsViewSpec E (ProductModel.left L R) (owns OL OR left right) left where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns, owns] at Hstate
    icases Hstate with ⟨%hv, Hleft, Hright⟩
    subst v
    isimp only [ProductModel.left,
      ProductModel.expectation_left L R s F hF] at Hcredit
    iapply hL.wp left s.1 n (ProductModel.leftCredit R s.2 F)
      (ProductModel.measurable_leftCredit R s.2 hF) _ $$ Hleft Hcredit
    iintro %t %I %hI Hleft Hcredit
    isimp only [← ProductModel.expectation_left L R (t, s.2) F hF] at Hcredit
    iexists (t, s.2), I
    isplit
    · ipureintro
      exact ⟨rfl, ⟨hI.1, R.refines_refl _⟩, ProductModel.encloses_left L R s.2 hI.2⟩
    isimp only [ViewOwns, owns, ProductModel.left]
    iframe Hleft Hright Hcredit

/-- Reading the second coordinate uses the same resource, with the other Tonelli order. -/
theorem right_viewSpec (E : CoPset) (L : Model Ω₁ S₁) (R : Model Ω₂ S₂)
    (OL : Val rT → S₁ → IProp GF) (OR : Val rT → S₂ → IProp GF)
    (hR : IsOracleSpec E R OR) (left right : Val rT) :
    IsViewSpec E (ProductModel.right L R) (owns OL OR left right) right where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns, owns] at Hstate
    icases Hstate with ⟨%hv, Hleft, Hright⟩
    subst v
    isimp only [ProductModel.right, ProductModel.left,
      ProductModel.expectation_right L R s F hF] at Hcredit
    iapply hR.wp right s.2 n (ProductModel.rightCredit L s.1 F)
      (ProductModel.measurable_rightCredit L s.1 hF) _ $$ Hright Hcredit
    iintro %t %I %hI Hright Hcredit
    isimp only [← ProductModel.expectation_right L R (s.1, t) F hF] at Hcredit
    iexists (s.1, t), I
    isplit
    · ipureintro
      exact ⟨rfl, ⟨L.refines_refl _, hI.1⟩, ProductModel.encloses_right L R s.1 hI.2⟩
    isimp only [ViewOwns, owns, ProductModel.right, ProductModel.left]
    iframe Hleft Hright Hcredit

/-- Sequential construction supplies both oracle handles with their full joint credit.
Local closure of the second program protects it under the first structural binder. -/
theorem payloadSpec (E : CoPset) (left right : Exp rT) (hright_lc : right.IsLocallyClosed)
    (L : Model Ω₁ S₁) (R : Model Ω₂ S₂) (i : S₁) (j : S₂)
    (OL : Val rT → S₁ → IProp GF) (OR : Val rT → S₂ → IProp GF)
    (hleft : IsLatentDistSpec E left L i OL) (hright : IsLatentDistSpec E right R j OR) :
    IsLatentPayloadSpec E (code left right) (ProductModel.left L R) (i, j)
      (pairOwns OL OR) where
  spec F hF := by
    iintro Hcredit
    isimp only [ProductModel.left,
      ProductModel.expectation_left L R (i, j) F hF] at Hcredit
    unfold code
    twp_bind left
    iapply hleft.wp (ProductModel.leftCredit R j F)
      (ProductModel.measurable_leftCredit R j hF) _ $$ Hcredit
    iintro %x %s %hs Hleft Hcredit
    twp_pure
    simp only [(Exp.open_lc 0 x.fst right hright_lc).symm]
    twp_bind right
    isimp only [← ProductModel.expectation_left L R (s, j) F hF,
      ProductModel.expectation_right L R (s, j) F hF] at Hcredit
    iapply hright.wp (ProductModel.rightCredit L s F)
      (ProductModel.measurable_rightCredit L s hF) _ $$ Hcredit
    iintro %y %t %ht Hright Hcredit
    twp_pure
    rw [show Exp.pair x.fst y.fst = Exp.ofVal (Val.pair x y) from rfl]
    iapply (tglWp_value (v := Val.pair x y))
    isimp only [← ProductModel.expectation_right L R (s, t) F hF] at Hcredit
    iexists (s, t)
    isplit
    · ipureintro
      exact ⟨hs, ht⟩
    isplitl [Hleft Hright]
    · isimp only [pairOwns, owns]
      iexists x, y
      iframe Hleft Hright
      ipureintro
      rfl
    isimp only [ProductModel.left]
    iframe Hcredit

end specification

end

end SampLib.LatentReal.Product
