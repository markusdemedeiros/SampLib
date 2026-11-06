import SampLib.Latent.LatentCoinSpec
import SampLib.Common.CoinComplement

/-! # Complementing a coin while retaining its complete latent posterior -/

open ProbLang MeasureTheory
open scoped ENNReal

namespace SampLib.LatentReal.LatentCoin

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω]

/-- Negation swaps the two result credits at each latent world. -/
theorem complement_credit (D : Model Ω S) (s : S) (φ : Ω → unitInterval)
    (G : Bool → Ω → ℝ≥0∞) :
    credit D s φ (fun bit x => G (!bit) x) =
      credit D s (fun x => unitInterval.symm (φ x)) G := by
  apply lintegral_congr
  intro x
  exact (RealCoin.lintegral_law _ _).symm.trans
    ((Complement.expectation_preservation (φ x) (fun bit => G bit x)).trans
      (RealCoin.lintegral_law _ _))

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- One call is negated; its source cache and arbitrary joint credit remain owned. -/
theorem complementSpec (E : CoPset) (D : Model Ω S)
    (owns : Val rT → S → IProp GF) (φ : Ω → unitInterval)
    (coin : Val rT → Val rT) (hcoin : IsLatentCoinSpec E D owns φ coin) :
    IsLatentCoinSpec E D owns (fun x => unitInterval.symm (φ x))
      (fun source => CoinComplement.callback (coin source)) where
  measurable_bias := unitInterval.continuous_symm.measurable.comp hcoin.measurable_bias
  spec source s G hG := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [← complement_credit D s φ G] at Hcredit
    twp_pure
    twp_bind pl(&(coin source).fst #())
    iapply hcoin.wp source s (fun bit x => G (!bit) x) (fun bit => hG (!bit)) _
      $$ Hstate Hcredit
    iintro %bit %t %hst Hstate Hcredit
    cases bit
    · twp_pures
      twp_value
      imodintro
      iapply post_return D owns source s t true G hst
      iframe Hstate Hcredit
    · twp_pures
      twp_value
      imodintro
      iapply post_return D owns source s t false G hst
      iframe Hstate Hcredit

end

end SampLib.LatentReal.LatentCoin
