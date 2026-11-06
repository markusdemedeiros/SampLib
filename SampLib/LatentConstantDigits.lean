import SampLib.LatentDigits

/-! # Constant digit streams

These callbacks exercise atomic laws: the all-ones stream represents one using
finite closed enclosures, although its intervals never become the exact point one.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentDigits

noncomputable section

/-- A callback that always returns the same bit, ignoring its prefix arguments. -/
def constantCallback {rT : Type} (b : Bool) : Val rT :=
  ⟨.lam (.lam (.lit (.bool b))), .lam (by is_lc), by is_lc⟩

section mathematics

open MeasureTheory

variable {Ω : Type} [MeasurableSpace Ω]

theorem nextLaw_constant (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Bool)
    (p : State μ (fun _ _ => b)) :
    DigitPosterior.nextLaw μ (fun _ _ => b) p.val = Measure.dirac b := by
  have := DigitPosterior.probability μ (fun _ _ => b) p.val p.property
  simp [DigitPosterior.nextLaw, Measure.map_const]

theorem constant_initial_law (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Bool) :
    (model μ (fun _ _ => b) (fun _ => measurable_const)).law
      (initial μ (fun _ _ => b)) = Measure.dirac (if b then (1 : ℝ) else 0) := by
  rw [initial_law]
  cases b <;> simp [Measure.map_const]

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open MeasureTheory (Measure IsProbabilityMeasure)

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- A concrete callback supplies the conditional law at every reachable prefix. -/
theorem constant_digitSpec (E : CoPset) (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Bool) :
    IsNextDigitSpec (GF := GF) E μ (fun _ _ => b) (fun _ => measurable_const)
      (constantCallback b) where
  coin p := by
    have := DigitPosterior.nextLaw_probability μ (fun _ => measurable_const) p.val p.property
    change IsDistSpec (GF := GF) E
      pl(&(constantCallback b).fst #int (UniformBag.rank p.val) #int (2 ^ p.val.length))
      (DigitPosterior.nextLaw μ (fun _ _ => b) p.val) Val.bool
    refine { spec := fun F _ => ?_ }
    rw [nextLaw_constant, MeasureTheory.lintegral_dirac]
    iintro Hcredit
    unfold constantCallback
    iterate 2 twp_pure
    twp_value
    imodintro
    iexists b
    iframe Hcredit
    itrivial

end specification

end

end SampLib.LatentDigits
