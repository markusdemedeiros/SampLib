import SampLib.Latent.LatentCoinSpec

/-! # Fresh ordinary programs inside an owned latent world -/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.LatentCoin

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- A fresh fixed-bias callback commutes with every source-posterior continuation. -/
theorem constantProgramSpec (E : CoPset) (D : Model Ω S) (owns : Val rT → S → IProp GF)
    (p : unitInterval) (e : Exp rT)
    (hcoin : IsDistSpec (GF := GF) E e (RealCoin.law p) Val.bool) :
    IsLatentCoinProgramSpec E D owns (fun _ => p) (fun _ => e) where
  measurable_bias := measurable_const
  spec source s G hG := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [credit_fixed_bias D s p G hG, ← RealCoin.lintegral_law] at Hcredit
    iapply hcoin.wp (fun b => ∫⁻ x, G b x ∂D.posterior s)
      (measurable_of_countable _) _ $$ Hcredit
    iintro %b Hcredit
    iapply post_return D owns source s s b G (D.refines_refl s)
    iframe Hstate Hcredit

end

end SampLib.LatentReal.LatentCoin
