import SampLib.Constants.Laws.LatentCoinReciprocal
import SampLib.Latent.LatentCoinSpec
import SampLib.Bernoulli.OneDivOnePlus
import SampLib.Core.Syntax.ClosedExp

/-! # A reciprocal factory over one owned latent world

The program threads the source ownership through every call and amplifies retry
credit uniformly by two, without averaging the source's conditional bias.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.CoinReciprocal

noncomputable section

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
