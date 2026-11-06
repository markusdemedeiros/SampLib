import SampLib.Latent.LatentVectorSpec
import SampLib.PSRN.Support.LatentRepresentedViews

/-! # Deferred vectors with deterministic coordinate representations -/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω] {n : ℕ}
local bi (IProp GF)

/-- The actual handles retain one physical world and each coordinate's exact interval. -/
structure IsRepresentedVectorSpec (E : CoPset) (e : Exp rT) (world : Model Ω S)
    (views : Fin n → Model Ω S) (Rs : ∀ i, Representation (views i)) (initial : S)
    (P : (Fin n → Val rT) → S → IProp GF) : Prop where
  sameWorld : ∀ i, world.SameWorld (views i)
  payload : IsLatentPayloadSpec E e world initial (VectorOwns P)
  coordinate : ∀ (handles : Fin n → Val rT) (i : Fin n),
    IsRepresentedViewSpec E (views i) (Rs i) (P handles) (handles i)

namespace IsRepresentedVectorSpec

variable {E : CoPset} {e : Exp rT} {world : Model Ω S}
  {views : Fin n → Model Ω S} {Rs : ∀ i, Representation (views i)} {initial : S}
  {P : (Fin n → Val rT) → S → IProp GF}

/-- Forgetting the certificate retains the entire original vector protocol. -/
theorem forget (h : IsRepresentedVectorSpec E e world views Rs initial P) :
    IsLatentVectorSpec E e world views initial P :=
  ⟨h.sameWorld, h.payload, fun handles i => (h.coordinate handles i).forget⟩

/-- Construction frames resources and assigns arbitrary credits to the joint latent world. -/
theorem wp (h : IsRepresentedVectorSpec E e world views Rs initial P)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) (Φ : Val rT → IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂world.posterior initial) -∗
      (∀ (handles : Fin n → Val rT) (t : S), ⌜world.refines initial t⌝ -∗
        P handles t -∗ ↯ (∫⁻ x, F x ∂world.posterior t) -∗ Φ (vectorVal handles)) -∗
      tglWp E e Φ := IsLatentVectorSpec.wp h.forget F hF Φ

end IsRepresentedVectorSpec

end

end SampLib.LatentReal
