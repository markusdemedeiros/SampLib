import SampLib.PSRN.Support.LatentMixture
import SampLib.PSRN.Support.LatentRealConstructors

/-! # An independent sign applied after constructing a deferred magnitude

The sign selects a copy of the same source world. The source is constructed once,
and only its returned cache is retained in the selected signed component.
-/

open ProbLang
open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal

namespace SampLib.LatentReal.Sign

noncomputable section

section mathematics

open MeasureTheory

variable {Ω S : Type} [MeasurableSpace Ω]

def inputCredit (p : unitInterval) (F : Ω ⊕ Ω → ℝ≥0∞) (x : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (p : ℝ) * F (Sum.inl x) + ENNReal.ofReal (1 - (p : ℝ)) * F (Sum.inr x)

theorem measurable_inputCredit (p : unitInterval) (F : Ω ⊕ Ω → ℝ≥0∞) (hF : Measurable F) :
    Measurable (inputCredit p F) :=
  (measurable_const.mul (hF.comp measurable_inl)).add
    (measurable_const.mul (hF.comp measurable_inr))

/-- Sign selection commutes with source expectation, preserving all latent dependencies. -/
theorem expectation_preservation (p : unitInterval) (μ : Measure Ω)
    (F : Ω ⊕ Ω → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, inputCredit p F x ∂μ) = ∫⁻ z, F z ∂MixtureModel.prior p μ μ := by
  rw [MixtureModel.expectation_preservation p μ μ F hF]
  unfold inputCredit
  have hm : Measurable (fun x => ENNReal.ofReal (p : ℝ) * F (Sum.inl x)) :=
    measurable_const.mul (hF.comp measurable_inl)
  have hl : Measurable (fun x => F (Sum.inl x)) := hF.comp measurable_inl
  have hr : Measurable (fun x => F (Sum.inr x)) := hF.comp measurable_inr
  rw [lintegral_add_left hm, lintegral_const_mul _ hl, lintegral_const_mul _ hr]

private theorem selector_expectation (p : unitInterval) (μ : Measure Ω)
    (F : Ω ⊕ Ω → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, inputCredit p F x ∂μ) =
      ∫⁻ b, (if b then ∫⁻ x, F (Sum.inl x) ∂μ
        else ∫⁻ x, F (Sum.inr x) ∂μ) ∂RealCoin.law p := by
  rw [expectation_preservation p μ F hF,
    MixtureModel.expectation_preservation p μ μ F hF, RealCoin.lintegral_law]
  rfl

end mathematics

private instance negate_closed {rT : Type} : ClosedExp (Occil.PSRN.negate : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.PSRN.negate, Exp.fv]

/-- The source is inserted after closing the single result binder. -/
def code {rT : Type} (e coin : Exp rT) : Exp rT :=
  .app (.lam (.cond coin (.bvar 0) (.app Occil.PSRN.negate (.bvar 0)))) e

private theorem code_eq {rT : Type} (e coin : Exp rT) (hcoin : coin.fv = ∅) :
    code e coin = pl(let source := &e; if &coin then source else &Occil.PSRN.negate source) := by
  have hc (k : ℕ) (x : Var) : Exp.closeRec k x coin = coin :=
    Exp.closeRec_fresh x coin k (by simp [hcoin])
  simp [code, hc, ClosedExp.closeRec, Exp.closeRec]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- An independent selector signs the one actual source draw after construction. -/
theorem latentDistSpec (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (hq : (p : ℝ) < 1) (e coin : Exp rT) (D : Model Ω S) (initial : S)
    (owns : Val rT → S → IProp GF) (hsource : IsLatentDistSpec E e D initial owns)
    (hcoin : IsDistSpec (GF := GF) E coin (RealCoin.law p) Val.bool)
    (hcoin_lc : coin.IsLocallyClosed) (hcoin_fv : coin.fv = ∅) :
    IsLatentDistSpec E
      pl(let source := &e; if &coin then source else &Occil.PSRN.negate source)
      (MixtureModel.model p D D.negate initial initial) .initial
      (Mixture.owns owns (negateOwns owns)) where
  oracle := Mixture.oracleSpec E p D D.negate initial initial owns (negateOwns owns)
    hsource.oracle (negate_oracleSpec E D owns hsource.oracle)
  spec F hF := by
    let _ : ClosedExp coin := ⟨hcoin_lc, hcoin_fv⟩
    iintro Hcredit
    rw [← code_eq e coin hcoin_fv]
    isimp only [MixtureModel.model, MixtureModel.posterior, Model.negate,
      ← expectation_preservation p (D.posterior initial) F hF] at Hcredit
    twp_bind e
    iapply hsource.wp (inputCredit p F) (measurable_inputCredit p F hF) _ $$ Hcredit
    iintro %source %t %ht Hstate Hcredit
    twp_pure
    isimp only [ClosedExp.openRec, ClosedExp.closeRec]
    twp_bind coin
    isimp only [selector_expectation p (D.posterior t) F hF] at Hcredit
    iapply hcoin.wp _ (measurable_of_countable _) _ $$ Hcredit
    iintro %b Hcredit
    cases b
    · twp_pure
      isimp only [Bool.false_eq_true, ite_false] at Hcredit
      iapply tglWp_wand
      isplitl [Hstate]
      · iapply twp_negate E owns source t $$ Hstate
      iintro %v Hstate
      iexists MixtureModel.State.right t
      isimp only [Mixture.owns, MixtureModel.model, MixtureModel.posterior,
        MeasureTheory.lintegral_map hF measurable_inr, Model.negate]
      iframe Hstate Hcredit
      ipureintro
      exact ⟨hq, ht⟩
    · twp_pures
      isimp only [ite_true] at Hcredit
      iapply (tglWp_value_of_toVal (Val.toVal?_fst source))
      iexists MixtureModel.State.left t
      isimp only [Mixture.owns, MixtureModel.model, MixtureModel.posterior,
        MeasureTheory.lintegral_map hF measurable_inl, ite_true]
      iframe Hstate Hcredit
      ipureintro
      exact ⟨hp, ht⟩

end specification

end

end SampLib.LatentReal.Sign
