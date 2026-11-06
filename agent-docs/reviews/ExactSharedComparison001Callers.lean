import SampLib.PSRN.Support.PSRNLess
import SampLib.Latent.LatentUniform
import SampLib.PSRN.Support.LatentUnaryViews

open ProbLang
open scoped ENNReal

namespace ReviewSharedComparison001

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib SampLib.LatentReal

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

theorem framed (E : CoPset) (Dleft Dright : Model Ω S)
    (hworld : Dleft.SameWorld Dright) (hl : Dleft.MeasurableError) (hr : Dright.MeasurableError)
    (P : S → IProp GF) (left right : Val rT)
    (hleft : IsViewSpec E Dleft P left) (hright : IsViewSpec E Dright P right)
    (s : S) (hne : ∀ᵐ x ∂Dleft.posterior s, Dleft.value x ≠ Dright.value x)
    (G : Bool → Ω → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) (R : IProp GF) :
    iprop(P s ∗ ↯ (∫⁻ x, Less.outputCredit Dleft Dright G x ∂Dleft.posterior s) ∗ R) ⊢
      tglWp E pl(&Occil.PSRN.less &left.fst &right.fst)
        (fun v : Val rT => iprop(Less.post Dleft Dright P s G v ∗ R)) := by
  iintro ⟨Hstate, Hcredit, HR⟩
  iapply tglWp_wand
  isplitl [Hstate Hcredit]
  · iapply Less.twp_less E Dleft Dright hworld hl hr P left right hleft hright s hne G hG
    iframe Hstate Hcredit
  iintro %v Hpost
  iframe Hpost HR

private theorem uniform_negate_distinct (p : List Bool) :
    ∀ᵐ x ∂LatentUniform.model.posterior p,
      LatentUniform.model.value x ≠ LatentUniform.model.negate.value x := by
  have hzero : ∀ᵐ x ∂DyadicPosterior.unitLaw, x ≠ (0 : ℝ) := by
    unfold DyadicPosterior.unitLaw
    exact MeasureTheory.Measure.ae_ne _ 0
  have hp := (DyadicPosterior.law_absolutelyContinuous_unit p).ae_le hzero
  filter_upwards [hp] with x hx
  change x ≠ -x
  intro h
  apply hx
  linarith

/-- The false comparison needs no credit, even with infinity requested on its null true branch. -/
example : (∫⁻ x, Less.outputCredit LatentUniform.model LatentUniform.model.negate
    (fun b _ => if b then ∞ else 0) x ∂LatentUniform.model.posterior []) = 0 := by
  change (∫⁻ x, Less.outputCredit LatentUniform.model LatentUniform.model.negate
    (fun b _ => if b then ∞ else 0) x ∂DyadicPosterior.law []) = 0
  rw [DyadicPosterior.law_nil]
  apply MeasureTheory.lintegral_eq_zero_of_ae_eq_zero
  have hs : MeasurableSet (Set.Ico (0 : ℝ) 1) := measurableSet_Ico
  filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) hs] with x hx
  simp [Less.outputCredit, Less.event, LatentUniform.model, Model.negate, hx.1]

section uniform

variable [ProbLangDist.IsUniformInt rT]

/-- Comparing U with -U rereads ONE source; no independent right draw is introduced. -/
example (E : CoPset) (source : Val rT) (p : List Bool)
    (G : Bool → ℝ → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) (R : IProp GF) :=
  framed E LatentUniform.model LatentUniform.model.negate
    ⟨fun _ => rfl, fun _ _ => Iff.rfl⟩
    (fun _ => measurable_const) (fun _ => measurable_const)
    (LatentUniform.owns source) source (negateVal source)
    ((LatentUniform.oracleSpec E).viewSpec E LatentUniform.model LatentUniform.owns source)
    (negate_viewSpec E LatentUniform.model (LatentUniform.owns source) source
      ((LatentUniform.oracleSpec E).viewSpec E LatentUniform.model LatentUniform.owns source))
    p (uniform_negate_distinct p) G hG R

example (E : CoPset) (source : Val rT) (p : List Bool) (R : IProp GF) :=
  framed E LatentUniform.model LatentUniform.model.negate
    ⟨fun _ => rfl, fun _ _ => Iff.rfl⟩
    (fun _ => measurable_const) (fun _ => measurable_const)
    (LatentUniform.owns source) source (negateVal source)
    ((LatentUniform.oracleSpec E).viewSpec E LatentUniform.model LatentUniform.owns source)
    (negate_viewSpec E LatentUniform.model (LatentUniform.owns source) source
      ((LatentUniform.oracleSpec E).viewSpec E LatentUniform.model LatentUniform.owns source))
    p (uniform_negate_distinct p) (fun _ _ => ∞) (fun _ => measurable_const) R

end uniform

#print axioms SampLib.LatentReal.Less.twp_less
#print axioms SampLib.LatentReal.Less.less_eventSpec
#print axioms SampLib.LatentReal.Less.expectation_preservation
#print axioms uniform_negate_distinct
#print axioms framed

end
end ReviewSharedComparison001
