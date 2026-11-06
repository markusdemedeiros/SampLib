import SampLib.LatentPayloadSpec
import SampLib.LatentViews
import SampLib.ListEncoding

/-! # Deferred vectors with one jointly owned latent world

Construction returns the actual list of oracle handles. Every coordinate view
consumes and returns the same whole-world ownership, permitting aliases and shared
normalizers while retaining arbitrary joint continuation credits.
-/

open ProbLang
open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

section mathematics

variable {Ω S : Type} [MeasurableSpace Ω] {n : ℕ}

/-- The mathematical vector consists of all real-valued coordinate views. -/
def vectorValue (views : Fin n → Model Ω S) (x : Ω) : Fin n → ℝ :=
  fun i => (views i).value x

theorem measurable_vectorValue (views : Fin n → Model Ω S) : Measurable (vectorValue views) :=
  measurable_pi_iff.2 fun i => (views i).measurable_value

/-- The joint output law, without factoring coordinate marginal laws. -/
def vectorLaw (world : Model Ω S) (views : Fin n → Model Ω S) (s : S) :
    Measure (Fin n → ℝ) := (world.posterior s).map (vectorValue views)

instance (world : Model Ω S) (views : Fin n → Model Ω S) (s : S) :
    IsProbabilityMeasure (vectorLaw world views s) := by
  unfold vectorLaw
  infer_instance

end mathematics

/-- Object-language list of coordinate-oracle handles. -/
def vectorVal {rT : Type} [ProbLangℝ rT] {n : ℕ} (handles : Fin n → Val rT) : Val rT :=
  listVal id (List.ofFn handles)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω] {n : ℕ}
local bi (IProp GF)

/-- The returned list and all its coordinates share exactly one physical world. -/
def VectorOwns (P : (Fin n → Val rT) → S → IProp GF) (v : Val rT) (s : S) : IProp GF :=
  iprop(∃ handles : Fin n → Val rT, ⌜v = vectorVal handles⌝ ∗ P handles s)

/-- A vector law includes actual construction and each coordinate's observation protocol. -/
structure IsLatentVectorSpec (E : CoPset) (e : Exp rT) (world : Model Ω S)
    (views : Fin n → Model Ω S) (initial : S)
    (P : (Fin n → Val rT) → S → IProp GF) : Prop where
  sameWorld : ∀ i, Model.SameWorld world (views i)
  payload : IsLatentPayloadSpec E e world initial (VectorOwns P)
  coordinate : ∀ (handles : Fin n → Val rT) (i : Fin n),
    IsViewSpec E (views i) (P handles) (handles i)

namespace IsLatentVectorSpec

/-- A caller receives the actual handles and the one shared, possibly refined state. -/
theorem wp {E : CoPset} {e : Exp rT} {world : Model Ω S}
    {views : Fin n → Model Ω S} {initial : S}
    {P : (Fin n → Val rT) → S → IProp GF}
    (h : IsLatentVectorSpec E e world views initial P)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) (Φ : Val rT → IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂world.posterior initial) -∗
      (∀ (handles : Fin n → Val rT) (t : S), ⌜world.refines initial t⌝ -∗
        P handles t -∗ ↯ (∫⁻ x, F x ∂world.posterior t) -∗ Φ (vectorVal handles)) -∗
      tglWp E e Φ := by
  iintro Hcredit Hcont
  iapply h.payload.wp F hF _ $$ Hcredit
  iintro %v %t %ht Hstate Hcredit
  isimp only [VectorOwns] at Hstate
  icases Hstate with ⟨%handles, %hv, Hstate⟩
  subst v
  iapply Hcont $$ %handles %t %ht Hstate Hcredit

end IsLatentVectorSpec

end specification

end

end SampLib.LatentReal
