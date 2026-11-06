import SampLib.Bernoulli.Laws.LogOnePlusFactory
import SampLib.Common.Laws.BernoulliMixture
import SampLib.Bernoulli.SampleGeometricBag
import SampLib.Bernoulli.Support.BagProduct
import SampLib.Bernoulli.Support.BagReciprocal

/-! # The lazy-uniform log(1+p) factory

The private bag is retained throughout the reciprocal factory. Its callback has
bias pU and the complete reciprocal has conditional bias 1/(1+pU); only then is
U integrated out. The outer p-coin gives the success mass log(1+p).
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LogOnePlusFactory

noncomputable section

section mathematics

open Set MeasureTheory

abbrev conditionalBias (p : unitInterval) := BagProduct.bias (fun _ => p) LatentBernoulli.bias
abbrev reciprocalBias (p : unitInterval) := BagReciprocal.bias (conditionalBias p)
abbrev successBias (p : unitInterval) := BagProduct.bias (fun _ => p) (reciprocalBias p)

private theorem measurable_conditionalBias (p : unitInterval) : Measurable (conditionalBias p) := by
  change Measurable (fun u => p * LatentBernoulli.bias u)
  exact measurable_const.mul LatentBernoulli.measurable_bias

private theorem measurable_reciprocalBias (p : unitInterval) : Measurable (reciprocalBias p) :=
  BagReciprocal.measurable_bias (measurable_conditionalBias p)

private theorem success_mass (p : unitInterval) :
    (∫⁻ u, ENNReal.ofReal (successBias p u : ℝ) ∂DyadicPosterior.unitLaw) =
      ENNReal.ofReal (bias p : ℝ) := by
  have hu : ∀ᵐ u ∂DyadicPosterior.unitLaw, u ∈ Ico 0 1 := ae_restrict_mem measurableSet_Ico
  have hcoe (u : ℝ) (hu : u ∈ Ico 0 1) :
      (successBias p u : ℝ) = (p : ℝ) / (1 + (p : ℝ) * u) := by
    change (p : ℝ) * (1 / (1 + (p : ℝ) * (LatentBernoulli.bias u : ℝ))) = _
    rw [LatentBernoulli.bias_coe hu]
    ring
  rw [lintegral_congr_ae (hu.mono fun u hu => congrArg ENNReal.ofReal (hcoe u hu))]
  exact lintegral p

/-- Continuation credit after the outer p-coin. -/
def outerCredit (p : unitInterval) (F : Bool → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then LatentBernoulli.credit [] (reciprocalBias p) (fun b _ => F b) else F false

/-- The complete conditional reciprocal is averaged after multiplying by the outer p. -/
theorem expectation (p : unitInterval) (F : Bool → ℝ≥0∞) :
    (∫⁻ b, outerCredit p F b ∂RealCoin.law p) = RealCoin.credit (bias p) F := by
  have hG : ∀ b, Measurable
      (BagProduct.inputCredit (reciprocalBias p) (fun b _ => F b) b) := by
    intro b
    cases b
    · exact measurable_const
    · exact LatentBernoulli.measurable_kernel (measurable_reciprocalBias p)
        (fun _ => measurable_const)
  have ho : (fun b => DyadicPosterior.credit []
      (BagProduct.inputCredit (reciprocalBias p) (fun b _ => F b) b)) = outerCredit p F := by
    funext b
    cases b
    · simp [BagProduct.inputCredit, outerCredit, DyadicPosterior.credit]
    · rfl
  have hp := BagProduct.expectation [] (fun _ => p) (reciprocalBias p) (fun b _ => F b)
  rw [LatentBernoulli.credit_fixed_bias [] p _ hG, ho] at hp
  have hm : Measurable (successBias p) := by
    change Measurable (fun u => p * reciprocalBias p u)
    exact measurable_const.mul (measurable_reciprocalBias p)
  have haverage := BernoulliMixture.expectation DyadicPosterior.unitLaw (successBias p) hm
    (bias p) (success_mass p) F
  rw [RealCoin.lintegral_law, ← hp]
  simpa only [LatentBernoulli.credit, LatentBernoulli.kernel, DyadicPosterior.credit,
    DyadicPosterior.law_nil] using haverage

end mathematics

private def callback {rT : Type} (coin : Val rT) (l : Loc) : Val rT :=
  ⟨.lam pl(if &coin.fst #() then &Occil.sampleGeometricBag #loc l #() else #false),
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

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem callback_spec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) (l : Loc) :
    UniformBag.IsCoinSpec (GF := GF) E l pl(&(callback coin l).fst #()) (conditionalBias p) where
  measurable_bias := measurable_conditionalBias p
  spec q G hG := by
    iintro Hcredit
    twp_pure
    isimp only [geometric_open]
    iapply BagProduct.twp_product E l (fun _ => p) LatentBernoulli.bias
      pl(&coin.fst #()) pl(&Occil.sampleGeometricBag #loc l #())
      (BagProduct.of_distSpec E l pl(&coin.fst #()) p hcoin)
      (SampleGeometricBag.sampleGeometricBag_coinSpec E l) q G hG $$ Hcredit

/-- Execute the private shared-U reciprocal, retaining the bag until the result returns. -/
theorem twp_logOnePlusFactory (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias p) F) -∗
      tglWp E pl(&Occil.logOnePlusFactory &coin.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iterate 2 twp_pure
  twp_bind pl(&coin.fst #())
  isimp only [← expectation p F] at Hcredit
  iapply (hcoin.wp (outerCredit p F) (measurable_of_finite _) _) $$ Hcredit
  iintro %outer Hcredit
  cases outer
  · twp_pures
    twp_value
    imodintro
    iexists false
    isimp only [outerCredit, Bool.false_eq_true, ite_false] at Hcredit
    iframe Hcredit
    itrivial
  · twp_pures
    twp_bind (Exp.alloc (Exp.ofVal (UniformBag.emptyVal : Val rT)))
    iapply twp_alloc
    iintro %l Hbag
    twp_pure
    isimp only [reciprocal_open, reciprocal_close, geometric_open, geometric_close]
    ieval (change _ ⊢ tglWp E pl(&Occil.oneDivOnePlus &(callback coin l).fst #()) _)
    have hrec := BagReciprocal.oneDivOnePlus_coinSpec E l (conditionalBias p)
      (callback coin l) (callback_spec E p coin hcoin l)
    have hnext := hrec.spec [] (fun b _ => F b) (fun _ => measurable_const)
    simp only [UniformBag.owns] at hnext
    isimp only [outerCredit, ite_true] at Hcredit
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

/-- The actual lazy-uniform factory has bias log(1+p), including p=0 and p=1. -/
theorem logOnePlusFactory_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.logOnePlusFactory &coin.fst #())
      (RealCoin.law (bias p)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_logOnePlusFactory E p coin hcoin F)

end specification

end

end SampLib.LogOnePlusFactory
