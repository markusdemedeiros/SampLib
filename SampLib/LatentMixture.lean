import SampLib.LatentMixtureModel
import SampLib.Samplers.RealCoin
import SampLib.SupportedSpec

/-! # Selecting between two deferred-real constructors

One selector chooses a whole component world. Both construction and subsequent
observations retain arbitrary credits on the selector-indexed joint latent space.
-/

open ProbLang
open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal

namespace SampLib.LatentReal.Mixture

noncomputable section

section mathematics

open MeasureTheory

/-- A zero-mass branch cannot be returned, including at either endpoint bias. -/
private theorem selector_support (p : unitInterval) :
    ∀ᵐ b ∂RealCoin.law p, if b then 0 < (p : ℝ) else (p : ℝ) < 1 := by
  apply ae_iff_of_countable.mpr
  intro b hb
  cases b with
  | false =>
    have hm : ENNReal.ofReal (1 - (p : ℝ)) ≠ 0 := by
      simpa [RealCoin.law, RealCoin.pmf] using hb
    exact sub_pos.mp (ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hm))
  | true =>
    have hm : ENNReal.ofReal (p : ℝ) ≠ 0 := by
      simpa [RealCoin.law, RealCoin.pmf] using hb
    exact ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hm)

/-- The sum-world expectation is the selector's expectation of component credits. -/
private theorem selector_expectation {Ω₁ Ω₂ : Type}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (p : unitInterval) (μ : Measure Ω₁) (ν : Measure Ω₂)
    (F : Ω₁ ⊕ Ω₂ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z ∂MixtureModel.prior p μ ν) =
      ∫⁻ b, (if b then ∫⁻ x, F (Sum.inl x) ∂μ
        else ∫⁻ x, F (Sum.inr x) ∂ν) ∂RealCoin.law p := by
  rw [MixtureModel.expectation_preservation p μ ν F hF, RealCoin.lintegral_law]
  rfl

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω₁ Ω₂ S₁ S₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
local bi (IProp GF)

/-- The selected component retains its entire physical oracle state. -/
def owns (OL : Val rT → S₁ → IProp GF) (OR : Val rT → S₂ → IProp GF)
    (v : Val rT) : MixtureModel.State S₁ S₂ → IProp GF
  | .initial => iprop(⌜False⌝)
  | .left s => OL v s
  | .right t => OR v t

/-- Reading the returned oracle preserves the selected component's full latent credit. -/
theorem oracleSpec (E : CoPset) (p : unitInterval) (L : Model Ω₁ S₁) (R : Model Ω₂ S₂)
    (i : S₁) (j : S₂) (OL : Val rT → S₁ → IProp GF) (OR : Val rT → S₂ → IProp GF)
    (hL : IsOracleSpec E L OL) (hR : IsOracleSpec E R OR) :
    IsOracleSpec E (MixtureModel.model p L R i j) (owns OL OR) where
  observe v s n F hF := by
    cases s with
    | initial =>
      iintro ⟨Hstate, _⟩
      isimp only [owns] at Hstate
      icases Hstate with %h
      exact h.elim
    | left s =>
      iintro ⟨Hstate, Hcredit⟩
      isimp only [owns] at Hstate
      isimp only [MixtureModel.model, MixtureModel.posterior,
        MeasureTheory.lintegral_map hF measurable_inl] at Hcredit
      iapply hL.wp v s n (fun x => F (Sum.inl x)) (hF.comp measurable_inl) _ $$
        Hstate Hcredit
      iintro %t %I %hI Hstate Hcredit
      iexists MixtureModel.State.left t, I
      isplit
      · ipureintro
        exact ⟨rfl, hI.1, MixtureModel.encloses_left p L R i j hI.2⟩
      isimp only [owns, MixtureModel.model, MixtureModel.posterior,
        MeasureTheory.lintegral_map hF measurable_inl]
      iframe Hstate Hcredit
    | right s =>
      iintro ⟨Hstate, Hcredit⟩
      isimp only [owns] at Hstate
      isimp only [MixtureModel.model, MixtureModel.posterior,
        MeasureTheory.lintegral_map hF measurable_inr] at Hcredit
      iapply hR.wp v s n (fun x => F (Sum.inr x)) (hF.comp measurable_inr) _ $$
        Hstate Hcredit
      iintro %t %I %hI Hstate Hcredit
      iexists MixtureModel.State.right t, I
      isplit
      · ipureintro
        exact ⟨rfl, hI.1, MixtureModel.encloses_right p L R i j hI.2⟩
      isimp only [owns, MixtureModel.model, MixtureModel.posterior,
        MeasureTheory.lintegral_map hF measurable_inr]
      iframe Hstate Hcredit

/-- An abstract Bernoulli selector composes two actual deferred constructors. -/
theorem latentDistSpec (E : CoPset) (p : unitInterval) (coin left right : Exp rT)
    (L : Model Ω₁ S₁) (R : Model Ω₂ S₂) (i : S₁) (j : S₂)
    (OL : Val rT → S₁ → IProp GF) (OR : Val rT → S₂ → IProp GF)
    (hcoin : IsDistSpec (GF := GF) E coin (RealCoin.law p) Val.bool)
    (hleft : IsLatentDistSpec E left L i OL)
    (hright : IsLatentDistSpec E right R j OR) :
    IsLatentDistSpec E pl(if &coin then &left else &right)
      (MixtureModel.model p L R i j) .initial (owns OL OR) where
  oracle := oracleSpec E p L R i j OL OR hleft.oracle hright.oracle
  spec F hF := by
    iintro Hcredit
    isimp only [MixtureModel.model, MixtureModel.posterior,
      selector_expectation p (L.posterior i) (R.posterior j) F hF] at Hcredit
    twp_bind coin
    iapply hcoin.wp_supported (fun b => if b then 0 < (p : ℝ) else (p : ℝ) < 1)
      (Set.to_countable _).measurableSet (selector_support p) _ (measurable_of_countable _) _ $$
      Hcredit
    iintro %b %hb Hcredit
    cases b with
    | false =>
      twp_pure
      isimp only [Bool.false_eq_true, ite_false] at Hcredit
      iapply hright.wp (fun x => F (Sum.inr x)) (hF.comp measurable_inr) _ $$ Hcredit
      iintro %v %t %ht Hstate Hcredit
      iexists MixtureModel.State.right t
      isplit
      · ipureintro
        exact ⟨hb, ht⟩
      isimp only [owns, MixtureModel.model, MixtureModel.posterior,
        MeasureTheory.lintegral_map hF measurable_inr]
      iframe Hstate Hcredit
    | true =>
      twp_pure
      isimp only [ite_true] at Hcredit
      iapply hleft.wp (fun x => F (Sum.inl x)) (hF.comp measurable_inl) _ $$ Hcredit
      iintro %v %t %ht Hstate Hcredit
      iexists MixtureModel.State.left t
      isplit
      · ipureintro
        exact ⟨hb, ht⟩
      isimp only [owns, MixtureModel.model, MixtureModel.posterior,
        MeasureTheory.lintegral_map hF measurable_inl]
      iframe Hstate Hcredit

end specification

end

end SampLib.LatentReal.Mixture
