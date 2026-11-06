import SampLib.LatentViews
import SampLib.LatentRational

/-! # Exact rational views of an existing latent world -/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω]

/-- A constant projection retains the entire source posterior and ownership. -/
def Model.constant (D : Model Ω S) (c : ℝ) : Model Ω S :=
  { D with
    value := fun _ => c
    measurable_value := measurable_const
    error := fun _ _ => 0
    error_tendsto := fun _ => Filter.Eventually.of_forall fun _ => tendsto_const_nhds }

theorem Model.sameWorld_constant (D : Model Ω S) (c : ℝ) :
    D.SameWorld (D.constant c) := ⟨fun _ => rfl, fun _ _ => Iff.rfl⟩

theorem Model.encloses_constant (D : Model Ω S) (s : S) (n : ℕ)
    (a b : ℤ) (hb : 0 < b) :
    (D.constant ((a : ℝ) / b)).Encloses s n (RationalInterval.point a b hb) := by
  apply Filter.Eventually.of_forall
  intro x
  refine ⟨(RationalInterval.contains_point _ _ _ _).mpr rfl, ?_⟩
  simp [RationalInterval.point, RationalInterval.lowerReal, RationalInterval.upperReal,
    Model.constant]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Reading the constant leaves every resource and the full joint credit intact. -/
theorem constant_viewSpec (E : CoPset) (D : Model Ω S) (P : S → IProp GF)
    (a b : ℤ) (hb : 0 < b) :
    IsViewSpec E (D.constant ((a : ℝ) / b)) P (LatentRational.value a b) where
  observe v s n F _ := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨%hv, Hstate⟩
    subst v
    unfold LatentRational.value
    twp_pures
    twp_value
    imodintro
    iexists s, RationalInterval.point a b hb
    iframe Hcredit
    isplitl []
    · ipureintro
      exact ⟨rfl, D.refines_refl s, D.encloses_constant s n a b hb⟩
    isimp only [ViewOwns]
    iframe Hstate

end specification

end

end SampLib.LatentReal
