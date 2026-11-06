import SampLib.LatentCoinSpec
import SampLib.Samplers.OneDivOnePlus
import SampLib.Syntax.ClosedExp

/-! # A reciprocal factory over one owned latent world

The reciprocal identity is applied at each latent point before integration. The
program threads the source ownership through every call and amplifies retry
credit uniformly by two, without averaging the source's conditional bias.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.CoinReciprocal

noncomputable section

section mathematics

open MeasureTheory
open LatentCoin

variable {Ω S : Type} [MeasurableSpace Ω]

def bias (φ : Ω → unitInterval) (x : Ω) : unitInterval := OneDivOnePlus.bias (φ x)

theorem measurable_bias {φ : Ω → unitInterval} (hφ : Measurable φ) :
    Measurable (bias φ) := by
  unfold bias OneDivOnePlus.bias EvenParity.bias
  fun_prop

/-- A failed input trial retries with doubled auxiliary credit. -/
def inputCredit (φ : Ω → unitInterval) (G : Bool → Ω → ℝ≥0∞)
    (ε : ℝ≥0∞) (b : Bool) : Ω → ℝ≥0∞ :=
  if b then G false else fun x => kernel (bias φ) G x + 2 * ε

private theorem measurable_inputCredit {φ : Ω → unitInterval} (hφ : Measurable φ)
    {G : Bool → Ω → ℝ≥0∞} (hG : ∀ b, Measurable (G b)) (ε : ℝ≥0∞) (b : Bool) :
    Measurable (inputCredit φ G ε b) := by
  cases b
  · exact (measurable_kernel (measurable_bias hφ) hG).add measurable_const
  · exact hG false

/-- Credit for the outer fair selector. -/
def selectorCredit (D : Model Ω S) (s : S) (φ : Ω → unitInterval)
    (G : Bool → Ω → ℝ≥0∞) (ε : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then ∫⁻ x, G true x ∂D.posterior s
  else credit D s φ (inputCredit φ G ε)

private theorem posterior_add_const (D : Model Ω S) (s : S) (F : Ω → ℝ≥0∞)
    (hF : Measurable F) (ε : ℝ≥0∞) :
    (∫⁻ x, F x + ε ∂D.posterior s) = (∫⁻ x, F x ∂D.posterior s) + ε := by
  rw [lintegral_add_left hF _]
  simp

/-- Pointwise reciprocal conservation pays at most one auxiliary retry credit. -/
theorem expectation (D : Model Ω S) (s : S) (φ : Ω → unitInterval) (hφ : Measurable φ)
    (G : Bool → Ω → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) (ε : ℝ≥0∞) :
    (∫⁻ b, selectorCredit D s φ G ε b ∂RealCoin.law VonNeumann.fairBias) ≤
      credit D s (bias φ) G + ε := by
  let K : Bool → Ω → ℝ≥0∞ := fun b x =>
    if b then G true x else kernel φ (inputCredit φ G ε) x
  have hK : ∀ b, Measurable (K b) := by
    intro b
    cases b
    · exact measurable_kernel hφ (measurable_inputCredit hφ hG ε)
    · exact hG true
  have hs : selectorCredit D s φ G ε = fun b => ∫⁻ x, K b x ∂D.posterior s := by
    funext b
    cases b <;> rfl
  have hp (x : Ω) : RealCoin.credit VonNeumann.fairBias (fun b => K b x) ≤
      kernel (bias φ) G x + ε := by
    simpa only [RealCoin.lintegral_law, OneDivOnePlus.fairCredit,
      OneDivOnePlus.coinCredit, kernel, inputCredit, ite_apply, bias, K] using
      OneDivOnePlus.expectation (φ x) (fun b => G b x) ε
  rw [RealCoin.lintegral_law, hs, ← credit_fixed_bias D s VonNeumann.fairBias K hK]
  calc
    _ ≤ ∫⁻ x, kernel (bias φ) G x + ε ∂D.posterior s := lintegral_mono hp
    _ = _ := posterior_add_const D s _ (measurable_kernel (measurable_bias hφ) hG) ε

end mathematics

private instance reciprocal_closed {rT : Type} :
    ClosedExp (Occil.oneDivOnePlus : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.oneDivOnePlus, Occil.fairCoin, Exp.fv]

/-- Capturing a callback after closing the unused unit binder preserves its free variables. -/
def callback {rT : Type} (coin : Val rT) : Val rT :=
  ⟨.lam (.app (.app Occil.oneDivOnePlus coin.fst) (.lit .unit)),
    .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open LatentCoin

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

private def property (E : CoPset) (D : Model Ω S) (owns : Val rT → S → IProp GF)
    (φ : Ω → unitInterval) (coin : Val rT → Val rT) (source : Val rT) : IProp GF :=
  iprop(∀ (s : S) (G : Bool → Ω → ℝ≥0∞), ⌜∀ b, Measurable (G b)⌝ -∗
    owns source s -∗ ↯ (credit D s (bias φ) G) -∗
      tglWp E pl(&Occil.oneDivOnePlus &(coin source).fst #()) (post D owns source s G))

private theorem twp_property (E : CoPset) (D : Model Ω S) (owns : Val rT → S → IProp GF)
    (φ : Ω → unitInterval) (coin : Val rT → Val rT)
    (hcoin : IsLatentCoinSpec E D owns φ coin) (source : Val rT)
    (ε : ℝ≥0∞) (hε : 0 < ε) : iprop(↯ ε) ⊢ property E D owns φ coin source := by
  iintro Hterm
  iapply ErrorCredit.Induction.simple (k := 2) hε (by norm_num) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩
  isimp only [property]
  iintro %s %G %hG Hstate Hcredit
  isimp only [ENNReal.coe_ofNat] at IH
  iterate 3 twp_pure
  isimp only [FairCoin.fairCoin_closeRec, FairCoin.fairCoin_openRec]
  twp_bind pl(&Occil.fairCoin #())
  icombine Hcredit Hterm as Htotal
  ihave Hsample := ErrorCredit.weaken
    (expectation D s φ hcoin.measurable_bias G hG ε) $$ Htotal
  iapply ((FairCoin.fairCoin_distSpec E).wp (selectorCredit D s φ G ε)
    (measurable_of_countable _) _) $$ Hsample
  iintro %select Hcredit
  cases select
  · twp_pures
    twp_bind pl(&(coin source).fst #())
    isimp only [selectorCredit, Bool.false_eq_true, ite_false] at Hcredit
    iapply hcoin.wp source s (inputCredit φ G ε)
      (measurable_inputCredit hcoin.measurable_bias hG ε) _ $$ Hstate Hcredit
    iintro %input %t %hst Hstate Hcredit
    cases input
    · twp_pure
      isimp only [inputCredit, Bool.false_eq_true, ite_false,
        posterior_add_const D t _
          (measurable_kernel (measurable_bias hcoin.measurable_bias) hG) (2 * ε)] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      twp_bind pl(&Occil.oneDivOnePlus &(coin source).fst #())
      iapply tglWp_wand
      isplitl [Hstate Hcredit Hterm IH]
      · ihave Hnext := IH $$ Hterm
        isimp only [property, credit] at Hnext
        iapply Hnext $$ %t %G %hG Hstate Hcredit
      iintro %v Hpost
      iapply (tglWp_value (v := v))
      iapply post_weaken D owns source s t G v hst $$ Hpost
    · twp_pures
      twp_value
      imodintro
      isimp only [inputCredit, ite_true] at Hcredit
      iapply post_return D owns source s t false G hst
      iframe Hstate Hcredit
  · twp_pures
    twp_value
    imodintro
    isimp only [selectorCredit, ite_true] at Hcredit
    iapply post_return D owns source s s true G (D.refines_refl s)
    iframe Hstate Hcredit

/-- Execute the existing reciprocal factory with a source-dependent, resourceful coin. -/
theorem twp_oneDivOnePlus (E : CoPset) (D : Model Ω S) (owns : Val rT → S → IProp GF)
    (φ : Ω → unitInterval) (coin : Val rT → Val rT)
    (hcoin : IsLatentCoinSpec E D owns φ coin) (source : Val rT) (s : S)
    (G : Bool → Ω → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    iprop(owns source s ∗ ↯ (credit D s (bias φ) G)) ⊢
      tglWp E pl(&Occil.oneDivOnePlus &(coin source).fst #()) (post D owns source s G) := by
  iintro ⟨Hstate, Hcredit⟩
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  ihave Hnext := twp_property E D owns φ coin hcoin source ε hε $$ Hterm
  isimp only [property] at Hnext
  iapply Hnext $$ %s %G %hG Hstate Hcredit

/-- The reciprocal callback preserves the source's whole latent world. -/
theorem reciprocal_coinSpec (E : CoPset) (D : Model Ω S)
    (owns : Val rT → S → IProp GF) (φ : Ω → unitInterval) (coin : Val rT → Val rT)
    (hcoin : IsLatentCoinSpec E D owns φ coin) :
    IsLatentCoinSpec E D owns (bias φ) (fun source => callback (coin source)) where
  measurable_bias := measurable_bias hcoin.measurable_bias
  spec source s G hG := by
    iintro ⟨Hstate, Hcredit⟩
    twp_pure
    isimp only [ClosedExp.openRec]
    iapply twp_oneDivOnePlus E D owns φ coin hcoin source s G hG
    iframe Hstate Hcredit

end specification

end

end SampLib.LatentReal.CoinReciprocal
