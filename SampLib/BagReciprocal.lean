import SampLib.UniformBagCoin
import SampLib.Samplers.OneDivOnePlus

/-! # A reciprocal factory conditional on a shared uniform

The callback's bias may depend on the same latent U at every invocation. The
pointwise reciprocal identity is integrated only after the complete factory,
while bag ownership and its posterior are threaded through each callback.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.BagReciprocal

noncomputable section

/-- The reciprocal transforms each conditional bias separately. -/
def bias (φ : ℝ → unitInterval) (u : ℝ) : unitInterval := OneDivOnePlus.bias (φ u)

theorem measurable_bias {φ : ℝ → unitInterval} (hφ : Measurable φ) : Measurable (bias φ) := by
  unfold bias OneDivOnePlus.bias EvenParity.bias
  fun_prop

/-- A failed input coin retries with doubled auxiliary credit. -/
def inputCredit (φ : ℝ → unitInterval) (G : Bool → ℝ → ℝ≥0∞)
    (ε : ℝ≥0∞) (b : Bool) : ℝ → ℝ≥0∞ :=
  if b then G false else fun u => LatentBernoulli.kernel (bias φ) G u + 2 * ε

private theorem measurable_inputCredit {φ : ℝ → unitInterval} (hφ : Measurable φ)
    {G : Bool → ℝ → ℝ≥0∞} (hG : ∀ b, Measurable (G b)) (ε : ℝ≥0∞) (b : Bool) :
    Measurable (inputCredit φ G ε b) := by
  cases b
  · exact (LatentBernoulli.measurable_kernel (measurable_bias hφ) hG).add measurable_const
  · exact hG false

/-- The outer fair selector either returns true or invokes the conditional callback. -/
def selectorCredit (p : List Bool) (φ : ℝ → unitInterval) (G : Bool → ℝ → ℝ≥0∞)
    (ε : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then DyadicPosterior.credit p (G true)
  else LatentBernoulli.credit p φ (inputCredit φ G ε)

/-- Lift the pointwise reciprocal conservation law without averaging the callback's bias. -/
theorem expectation (p : List Bool) (φ : ℝ → unitInterval) (hφ : Measurable φ)
    (G : Bool → ℝ → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) (ε : ℝ≥0∞) :
    (∫⁻ b, selectorCredit p φ G ε b ∂RealCoin.law VonNeumann.fairBias) ≤
      LatentBernoulli.credit p (bias φ) G + ε := by
  let K : Bool → ℝ → ℝ≥0∞ := fun b u =>
    if b then G true u else LatentBernoulli.kernel φ (inputCredit φ G ε) u
  have hK : ∀ b, Measurable (K b) := by
    intro b
    cases b
    · exact LatentBernoulli.measurable_kernel hφ (measurable_inputCredit hφ hG ε)
    · exact hG true
  have hs : selectorCredit p φ G ε = fun b => DyadicPosterior.credit p (K b) := by
    funext b
    cases b <;> rfl
  have hp (u : ℝ) : RealCoin.credit VonNeumann.fairBias (fun b => K b u) ≤
      LatentBernoulli.kernel (bias φ) G u + ε := by
    simpa only [RealCoin.lintegral_law, OneDivOnePlus.fairCredit, OneDivOnePlus.coinCredit,
      LatentBernoulli.kernel, inputCredit, ite_apply, bias, K] using
      OneDivOnePlus.expectation (φ u) (fun b => G b u) ε
  rw [RealCoin.lintegral_law, hs,
    ← LatentBernoulli.credit_fixed_bias p VonNeumann.fairBias K hK]
  calc
    _ ≤ DyadicPosterior.credit p (fun u => LatentBernoulli.kernel (bias φ) G u + ε) :=
      MeasureTheory.lintegral_mono hp
    _ = _ := LatentBernoulli.posterior_add_const p _
      (LatentBernoulli.measurable_kernel (measurable_bias hφ) hG) ε

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private def property (E : CoPset) (l : Loc) (φ : ℝ → unitInterval) (coin : Val rT) :
    IProp GF := iprop(∀ (p : List Bool) (G : Bool → ℝ → ℝ≥0∞),
  ⌜∀ b, Measurable (G b)⌝ -∗ UniformBag.owns l p -∗
    ↯ (LatentBernoulli.credit p (bias φ) G) -∗
      tglWp E pl(&Occil.oneDivOnePlus &coin.fst #()) (UniformBag.coinPost l p G))

private theorem twp_property (E : CoPset) (l : Loc) (φ : ℝ → unitInterval) (coin : Val rT)
    (hcoin : UniformBag.IsCoinSpec (GF := GF) E l pl(&coin.fst #()) φ)
    (ε : ℝ≥0∞) (hε : 0 < ε) : iprop(↯ ε) ⊢ property E l φ coin := by
  iintro Hterm
  iapply ErrorCredit.Induction.simple (k := 2) hε (by norm_num) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩
  isimp only [property]
  iintro %p %G %hG Hbag Hcredit
  isimp only [ENNReal.coe_ofNat] at IH
  iterate 3 twp_pure
  isimp only [FairCoin.fairCoin_closeRec, FairCoin.fairCoin_openRec]
  twp_bind pl(&Occil.fairCoin #())
  icombine Hcredit Hterm as Htotal
  ihave Hsample := ErrorCredit.weaken
    (expectation p φ hcoin.measurable_bias G hG ε) $$ Htotal
  iapply ((FairCoin.fairCoin_distSpec E).wp (selectorCredit p φ G ε)
    (measurable_of_finite _) _) $$ Hsample
  iintro %select Hcredit
  cases select
  · twp_pures
    twp_bind pl(&coin.fst #())
    isimp only [selectorCredit, Bool.false_eq_true, ite_false] at Hcredit
    iapply (hcoin.wp p (inputCredit φ G ε)
      (measurable_inputCredit hcoin.measurable_bias hG ε) _) $$ Hbag Hcredit
    iintro %input %q %hpq Hbag Hcredit
    cases input
    · twp_pure
      isimp only [inputCredit, Bool.false_eq_true, ite_false,
        LatentBernoulli.posterior_add_const q _
          (LatentBernoulli.measurable_kernel (measurable_bias hcoin.measurable_bias) hG)
          (2 * ε)] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      twp_bind pl(&Occil.oneDivOnePlus &coin.fst #())
      iapply tglWp_wand
      isplitl [Hbag Hcredit Hterm IH]
      · ihave Hnext := IH $$ Hterm
        isimp only [property, LatentBernoulli.credit] at Hnext
        iapply Hnext $$ %q %G %hG Hbag Hcredit
      iintro %v Hpost
      iapply (tglWp_value (v := v))
      iapply UniformBag.coinPost_weaken l p q G v hpq $$ Hpost
    · twp_pures
      twp_value
      imodintro
      isimp only [inputCredit, ite_true] at Hcredit
      iapply UniformBag.coinPost_return l p q false G hpq
      iframe Hbag Hcredit
  · twp_pures
    twp_value
    imodintro
    isimp only [selectorCredit, ite_true] at Hcredit
    iapply UniformBag.coinPost_return l p p true G (List.prefix_refl _)
    iframe Hbag Hcredit

/-- Execute the existing reciprocal factory with a conditional resourceful callback. -/
theorem twp_oneDivOnePlus (E : CoPset) (l : Loc) (φ : ℝ → unitInterval) (coin : Val rT)
    (hcoin : UniformBag.IsCoinSpec (GF := GF) E l pl(&coin.fst #()) φ)
    (p : List Bool) (G : Bool → ℝ → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    iprop(UniformBag.owns l p ∗ ↯ (LatentBernoulli.credit p (bias φ) G)) ⊢
      tglWp E pl(&Occil.oneDivOnePlus &coin.fst #()) (UniformBag.coinPost l p G) := by
  iintro ⟨Hbag, Hcredit⟩
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  ihave Hnext := twp_property E l φ coin hcoin ε hε $$ Hterm
  isimp only [property] at Hnext
  iapply Hnext $$ %p %G %hG Hbag Hcredit

/-- Reusable conditional reciprocal kernel on the original shared uniform. -/
theorem oneDivOnePlus_coinSpec (E : CoPset) (l : Loc) (φ : ℝ → unitInterval) (coin : Val rT)
    (hcoin : UniformBag.IsCoinSpec (GF := GF) E l pl(&coin.fst #()) φ) :
    UniformBag.IsCoinSpec (GF := GF) E l pl(&Occil.oneDivOnePlus &coin.fst #()) (bias φ) where
  measurable_bias := measurable_bias hcoin.measurable_bias
  spec := twp_oneDivOnePlus E l φ coin hcoin

end specification

end

end SampLib.BagReciprocal
