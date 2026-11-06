import SampLib.PSRN.Support.UniformThreshold
import SampLib.PSRN.Syntax.PSRNCoin
import SampLib.PSRN.Support.PSRNLess
import SampLib.PSRN.Support.LatentProduct
import SampLib.PSRN.Support.LatentMixtureModel

/-! # Conditional coins from a deferred real

A fresh independent comparison uniform gives the clamped source bias. The product
world is temporary: the result retains the original source and its full joint credit.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.Coin

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

private theorem twp_comparison (E : CoPset) (D : Model Ω S) (herror : D.MeasurableError)
    (owns : Val rT → S → IProp GF) (horacle : IsOracleSpec E D owns)
    (source : Val rT) (s : S) (G : Bool → Ω → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    iprop(owns source s ∗ ↯ (LatentCoin.credit D s
      (fun x => LatentBernoulli.bias (D.value x)) G)) ⊢
      tglWp E pl(&Occil.PSRN.less (&Occil.PSRN.newUniform #()) &source.fst)
        (LatentCoin.post D owns source s G) := by
  have hallocate : (∫⁻ z, UniformThreshold.kernel D G z
      ∂ProductModel.posterior LatentUniform.model D ([], s)) =
      DyadicPosterior.credit [] (ProductModel.leftCredit D s (UniformThreshold.kernel D G)) :=
    ProductModel.expectation_left LatentUniform.model D ([], s)
      (UniformThreshold.kernel D G) (UniformThreshold.measurable_kernel D G hG)
  have hkernel : UniformThreshold.kernel D G =
      Less.outputCredit (ProductModel.left LatentUniform.model D)
        (ProductModel.right LatentUniform.model D) (fun b z => G b z.2) := rfl
  iintro ⟨Hsource, Hcredit⟩
  isimp only [← UniformThreshold.expectation D s G hG, hallocate] at Hcredit
  twp_bind pl(&Occil.PSRN.newUniform #())
  iapply tglWp_wand
  isplitl [Hcredit]
  · have hnew := LatentUniform.twp_newUniform (rT := rT) (GF := GF) E
      (ProductModel.leftCredit D s (UniformThreshold.kernel D G))
    iapply hnew $$ Hcredit
  iintro %uniform ⟨Huniform, Hcredit⟩
  isimp only [← hallocate] at Hcredit
  isimp only [Exp.ofVal]
  iapply tglWp_wand
  isplitl [Huniform Hsource Hcredit]
  · iapply Less.twp_less E (ProductModel.left LatentUniform.model D)
      (ProductModel.right LatentUniform.model D) (ProductModel.sameWorld _ _)
      (Model.MeasurableError.product_left (fun _ => measurable_const))
      (Model.MeasurableError.product_right herror)
      (Product.owns LatentUniform.owns owns uniform source) uniform source
      (Product.left_viewSpec E LatentUniform.model D LatentUniform.owns owns
        (LatentUniform.oracleSpec E) uniform source)
      (Product.right_viewSpec E LatentUniform.model D LatentUniform.owns owns
        horacle uniform source)
      ([], s) (UniformThreshold.ae_distinct D s)
      (fun b z => G b z.2) (fun b => (hG b).comp measurable_snd)
    isimp only [hkernel, ProductModel.left] at Hcredit
    isimp only [Product.owns, ProductModel.left]
    iframe Huniform Hsource Hcredit
  iintro %result Hpost
  isimp only [Less.post] at Hpost
  icases Hpost with ⟨%b, %t, %ht, Hstate, Hcredit⟩
  isimp only [Product.owns] at Hstate
  icases Hstate with ⟨Huniform, Hsource⟩
  isimp only [ProductModel.left, UniformThreshold.marginal_credit D t.1 t.2 (G b) (hG b)] at Hcredit
  isimp only [LatentCoin.post]
  iexists b, t.2
  iframe Hsource Hcredit
  ipureintro
  exact ⟨ht.1, ht.2.1.2⟩

/-- The actual scalar coin program preserves arbitrary source-dependent continuation credit. -/
theorem twp_coin (E : CoPset) (D : Model Ω S) (herror : D.MeasurableError)
    (owns : Val rT → S → IProp GF) (horacle : IsOracleSpec E D owns)
    (source : Val rT) (s : S) (G : Bool → Ω → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    iprop(owns source s ∗ ↯ (LatentCoin.credit D s
      (fun x => LatentBernoulli.bias (D.value x)) G)) ⊢
      tglWp E pl(&Occil.PSRN.coin &source.fst #()) (LatentCoin.post D owns source s G) := by
  iintro H
  iapply Program.twp_open E source _
  iapply twp_comparison E D herror owns horacle source s G hG $$ H

/-- Every finite real source is supported; outside [0,1], the comparison clamps its bias. -/
theorem coin_programSpec (E : CoPset) (D : Model Ω S) (herror : D.MeasurableError)
    (owns : Val rT → S → IProp GF) (horacle : IsOracleSpec E D owns) :
    IsLatentCoinProgramSpec E D owns (fun x => LatentBernoulli.bias (D.value x))
      (fun source => pl(&Occil.PSRN.coin &source.fst #())) where
  measurable_bias := LatentBernoulli.measurable_bias.comp D.measurable_value
  spec source s G hG := twp_coin E D herror owns horacle source s G hG

/-- The same conditional contract is reusable through the unit-callback interface. -/
theorem coin_spec (E : CoPset) (D : Model Ω S) (herror : D.MeasurableError)
    (owns : Val rT → S → IProp GF) (horacle : IsOracleSpec E D owns) :
    IsLatentCoinSpec E D owns (fun x => LatentBernoulli.bias (D.value x)) Program.value where
  measurable_bias := LatentBernoulli.measurable_bias.comp D.measurable_value
  spec source s G hG := by
    iintro H
    iapply Program.twp_open_value E source _
    iapply twp_comparison E D herror owns horacle source s G hG $$ H

end

end SampLib.LatentReal.Coin
