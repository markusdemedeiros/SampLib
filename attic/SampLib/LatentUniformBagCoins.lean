import SampLib.Latent.LatentCoinSpec
import SampLib.Latent.LatentUniform
import SampLib.Bernoulli.SampleGeometricBag

/-! # A geometric-bag callback retains its shared uniform posterior -/

open ProbLang MeasureTheory
open scoped ENNReal

namespace SampLib.LatentReal.UniformBagCoins

private instance geometric_closed {rT : Type} :
    ClosedExp (Occil.sampleGeometricBag : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

/-- The literal callback used by beta rejection after allocating its shared bag. -/
def value {rT : Type} (l : Loc) : Val rT :=
  ⟨pl(fun u, &Occil.sampleGeometricBag #loc l #()), .lam (by is_lc), by is_lc⟩

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The ignored argument is only a handle; ownership remains the one physical bag. -/
theorem coinSpec (E : CoPset) (l : Loc) :
    IsLatentCoinSpec E LatentUniform.model
      (fun (_ : Val rT) p => (UniformBag.owns l p : IProp GF)) LatentBernoulli.bias
      (fun _ => value l) where
  measurable_bias := LatentBernoulli.measurable_bias
  spec source p G hG := by
    iintro ⟨Hbag, Hcredit⟩
    have hcredit : LatentCoin.credit LatentUniform.model p LatentBernoulli.bias G =
        LatentBernoulli.credit p LatentBernoulli.bias G := rfl
    isimp only [hcredit] at Hcredit
    twp_pure
    isimp only [ClosedExp.openRec, ClosedExp.closeRec]
    iapply (SampleGeometricBag.sampleGeometricBag_coinSpec E l).wp p G hG _ $$ Hbag Hcredit
    iintro %bit %q %hpq Hbag Hcredit
    have hcredit : DyadicPosterior.credit q (G bit) =
        ∫⁻ x, G bit x ∂LatentUniform.model.posterior q := rfl
    isimp only [hcredit] at Hcredit
    iapply LatentCoin.post_return LatentUniform.model _ source p q bit G hpq
    iframe Hbag Hcredit

end

end SampLib.LatentReal.UniformBagCoins
