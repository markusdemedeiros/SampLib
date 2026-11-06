import SampLib.Bernoulli.Laws.ArctanFactory
import SampLib.Bernoulli.SampleGeometricBag
import SampLib.Bernoulli.Support.BagProduct
import SampLib.Bernoulli.Support.BagReciprocal
import SampLib.Common.Laws.BernoulliMixture

/-! # The arctangent ratio factory over a shared lazy uniform

Both geometric coins use the same bag. Products are formed conditionally on its
latent U, the reciprocal is completed, and only then is U averaged out.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.ArctanOverPFactory

noncomputable section

abbrev bias := ArctanFactory.ratio

def productBias (p : unitInterval) (u : ℝ) : unitInterval :=
  p * (p * (LatentBernoulli.bias u * LatentBernoulli.bias u))

def conditionalBias (p : unitInterval) := BagReciprocal.bias (productBias p)

private theorem measurable_productBias (p : unitInterval) : Measurable (productBias p) := by
  unfold productBias
  exact measurable_const.mul (measurable_const.mul
    (LatentBernoulli.measurable_bias.mul LatentBernoulli.measurable_bias))

/-- The reciprocal is integrated only after all reads of the same U have completed. -/
theorem expectation (p : unitInterval) (F : Bool → ℝ≥0∞) :
    LatentBernoulli.credit [] (conditionalBias p) (fun b _ => F b) =
      RealCoin.credit (bias p) F := by
  simp only [LatentBernoulli.credit, DyadicPosterior.credit, DyadicPosterior.law_nil]
  change (∫⁻ u, RealCoin.credit (conditionalBias p u) F ∂DyadicPosterior.unitLaw) = _
  have hm := BagReciprocal.measurable_bias (measurable_productBias p)
  apply BernoulliMixture.expectation DyadicPosterior.unitLaw (conditionalBias p) hm (bias p) _ F
  have hu : ∀ᵐ u ∂DyadicPosterior.unitLaw, u ∈ Set.Ico 0 1 :=
    MeasureTheory.ae_restrict_mem measurableSet_Ico
  have heq (u : ℝ) (hu : u ∈ Set.Ico 0 1) :
      (conditionalBias p u : ℝ) = 1 / (1 + ((p : ℝ) * u) ^ 2) := by
    change 1 / (1 + (p : ℝ) * (p * (LatentBernoulli.bias u * LatentBernoulli.bias u))) = _
    rw [LatentBernoulli.bias_coe hu]
    congr 2
    ring
  rw [MeasureTheory.lintegral_congr_ae
    (hu.mono fun u hu => congrArg ENNReal.ofReal (heq u hu))]
  exact ArctanFactory.success_mass p

private def callback {rT : Type} (coin : Val rT) (l : Loc) : Val rT :=
  ⟨.lam pl(if &coin.fst #() then if &coin.fst #() then
      if &Occil.sampleGeometricBag #loc l #() then
        &Occil.sampleGeometricBag #loc l #() else #false else #false else #false),
    .lam (by is_lc), by is_lc⟩

private theorem reciprocal_open {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.oneDivOnePlus = Occil.oneDivOnePlus :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem reciprocal_close {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.oneDivOnePlus : Exp rT) = Occil.oneDivOnePlus :=
  Exp.closeRec_fresh x _ k (by simp [Occil.oneDivOnePlus, Exp.fv, FairCoin.fairCoin_fv])

private theorem geometric_open {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.sampleGeometricBag = Occil.sampleGeometricBag :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem geometric_close {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.sampleGeometricBag : Exp rT) = Occil.sampleGeometricBag :=
  Exp.closeRec_fresh x _ k (by
    simp [Occil.sampleGeometricBag, Occil.uniformBagStep, Occil.newUniformBag,
      Exp.fv, FairCoin.fairCoin_fv])

theorem arctanOverPFactory_fv {rT : Type} :
    (Occil.arctanOverPFactory : Exp rT).fv = ∅ := by
  simp [Occil.arctanOverPFactory, Occil.oneDivOnePlus, Occil.sampleGeometricBag,
    Occil.uniformBagStep, Occil.newUniformBag, Exp.fv, FairCoin.fairCoin_fv]

@[simp] theorem arctanOverPFactory_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.arctanOverPFactory = Occil.arctanOverPFactory :=
  (Exp.open_lc k e _ (by is_lc)).symm

@[simp] theorem arctanOverPFactory_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.arctanOverPFactory : Exp rT) = Occil.arctanOverPFactory :=
  Exp.closeRec_fresh x _ k (by simp [arctanOverPFactory_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem inline_product_spec (E : CoPset) (l : Loc) (φ ψ : ℝ → unitInterval)
    (left right : Exp rT)
    (hleft : UniformBag.IsCoinSpec (GF := GF) E l left φ)
    (hright : UniformBag.IsCoinSpec (GF := GF) E l right ψ) :
    UniformBag.IsCoinSpec (GF := GF) E l pl(if &left then &right else #false)
      (BagProduct.bias φ ψ) where
  measurable_bias := hleft.measurable_bias.mul hright.measurable_bias
  spec := BagProduct.twp_product E l φ ψ left right hleft hright

private theorem callback_spec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) (l : Loc) :
    UniformBag.IsCoinSpec (GF := GF) E l pl(&(callback coin l).fst #())
      (productBias p) := by
  have hi := BagProduct.of_distSpec E l pl(&coin.fst #()) p hcoin
  have hg := SampleGeometricBag.sampleGeometricBag_coinSpec (rT := rT) (GF := GF) E l
  have hs : UniformBag.IsCoinSpec (GF := GF) E l _ (productBias p) :=
    inline_product_spec E l _ _ _ _ hi
    (inline_product_spec E l _ _ _ _ hi (inline_product_spec E l _ _ _ _ hg hg))
  refine ⟨hs.measurable_bias, ?_⟩
  intro q G hG
  iintro Hcredit
  twp_pure
  simp only [geometric_open]
  iapply hs.spec q G hG $$ Hcredit

/-- The actual cached-uniform algorithm realizes the continuous atan(p)/p extension. -/
theorem arctanOverPFactory_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.arctanOverPFactory &coin.fst #())
      (RealCoin.law (bias p)) Val.bool where
  spec F _ := by
    iintro Hcredit
    isimp only [RealCoin.lintegral_law, ← expectation p F] at Hcredit
    twp_pures
    twp_bind (Exp.alloc (Exp.ofVal (UniformBag.emptyVal : Val rT)))
    iapply twp_alloc
    iintro %l Hbag
    twp_pure
    simp only [reciprocal_open, reciprocal_close, geometric_open, geometric_close]
    have hs : UniformBag.IsCoinSpec (GF := GF) E l _ (conditionalBias p) :=
      BagReciprocal.oneDivOnePlus_coinSpec E l (productBias p)
      (callback coin l) (callback_spec E p coin hcoin l)
    have hnext := hs.spec [] (fun b _ => F b) (fun _ => measurable_const)
    simp only [UniformBag.owns, callback] at hnext
    iapply tglWp_wand
    isplitl [Hbag Hcredit]
    · iapply hnext
      iframe Hbag Hcredit
    iintro %v Hpost
    isimp only [UniformBag.coinPost] at Hpost
    ihave ⟨%b, %q, %hq, Hbag, Hcredit⟩ := Hpost
    rcases hq with ⟨rfl, _⟩
    isimp only [DyadicPosterior.credit, MeasureTheory.lintegral_const,
      MeasureTheory.measure_univ, mul_one] at Hcredit
    iexists b
    iframe Hcredit
    itrivial

end specification

end

end SampLib.ArctanOverPFactory
