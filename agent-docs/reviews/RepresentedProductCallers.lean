import SampLib.PSRN.Support.LatentRepresentedProduct
import SampLib.PSRN.Support.LatentRepresentedVectorSpec

open ProbLang
open scoped ENNReal

namespace RepresentedProductCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib.LatentReal

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω₁ Ω₂ S₁ S₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
local bi (IProp GF)

example (E : CoPset) (L : Model Ω₁ S₁) (R : Model Ω₂ S₂)
    (repr : Representation L) (OL : Val rT → S₁ → IProp GF) (OR : Val rT → S₂ → IProp GF)
    (h : IsRepresentedOracleSpec E L repr OL) (left right : Val rT) :=
  Product.left_representedViewSpec E L R repr OL OR h left right

example (E : CoPset) (L : Model Ω₁ S₁) (R : Model Ω₂ S₂)
    (repr : Representation R) (OL : Val rT → S₁ → IProp GF) (OR : Val rT → S₂ → IProp GF)
    (h : IsRepresentedOracleSpec E R repr OR) (left right : Val rT) :=
  Product.right_representedViewSpec E L R repr OL OR h left right

example {Ω S : Type} [MeasurableSpace Ω] {n : ℕ} (E : CoPset) (e : Exp rT)
    (D : Model Ω S) (views : Fin n → Model Ω S) (Rs : ∀ i, Representation (views i))
    (s : S) (P : (Fin n → Val rT) → S → IProp GF)
    (h : IsRepresentedVectorSpec E e D views Rs s P)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) (Φ : Val rT → IProp GF) :=
  IsRepresentedVectorSpec.wp h F hF Φ

example {Ω S : Type} [MeasurableSpace Ω] {n : ℕ} (E : CoPset) (e : Exp rT)
    (D : Model Ω S) (views : Fin n → Model Ω S) (Rs : ∀ i, Representation (views i))
    (s : S) (P : (Fin n → Val rT) → S → IProp GF)
    (h : IsRepresentedVectorSpec E e D views Rs s P) (Φ : Val rT → IProp GF) :=
  IsRepresentedVectorSpec.wp h (fun _ => ∞) measurable_const Φ

#print axioms Product.left_representedViewSpec
#print axioms Product.right_representedViewSpec
#print axioms IsRepresentedVectorSpec.forget
#print axioms IsRepresentedVectorSpec.wp

end

end RepresentedProductCallers
